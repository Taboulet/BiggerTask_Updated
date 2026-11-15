#include <QApplication>
#include <QMainWindow>
#include <QPushButton>
#include <QVBoxLayout>
#include <QHBoxLayout>
#include <QLabel>
#include <QFileDialog>
#include <QDoubleSpinBox>
#include <QSpinBox>
#include <QCheckBox>
#include <QJsonArray>
#include <QJsonObject>
#include <QJsonDocument>
#include <QFile>
#include <QWidget>
#include <QThread>
#include <QIcon>
#include <QMenu>
#include <QMessageBox>
#include <QStandardPaths>
#include <QDir>
#include <QDialog>
#include <QDialogButtonBox>
#include <QTimer>
#include <QEventLoop>
#include <QMetaType>

#include <atomic>
#include <vector>
#include <climits>
#include <ctime>
#include <unordered_set>
#include <set>
#include <algorithm>
#include <cmath>
#include <thread>
#include <chrono>
#include <map>
#include <poll.h>
#include <unistd.h>
#include <linux/input-event-codes.h>
#include <libei.h>
#include <liboeffis.h>

#include <X11/Xlib.h>
#include <X11/keysym.h>
#include <X11/XKBlib.h>
#include <X11/extensions/XInput2.h>
#include <X11/extensions/XTest.h>
#include <X11/extensions/Xrandr.h>

// ---------- Event & Monitor models ----------
struct Event {
    enum Type { MouseMove, MouseButton, Key } type;
    std::int64_t ms_since_start{0};
    int x{0}, y{0};
    int button{0};
    bool pressed{false};
    unsigned int keycode{0};
    unsigned int evdevCode{0}; // Linux input-event code; zero for legacy .recq files
    QString monitor;
    int relx{0}, rely{0};
};

struct MonitorInfo {
    QString name;
    int x, y, width, height;
};

// ---------- Display session detection ----------
// Do not mistake an XWayland DISPLAY for a complete X11 desktop session.
// XInput2/XTest only cover X11 clients and cannot implement global Wayland input.
static bool isWaylandSession() {
    const QByteArray sessionType = qgetenv("XDG_SESSION_TYPE").trimmed().toLower();

    // Prefer the session manager's explicit type when available. Some launchers
    // leave WAYLAND_DISPLAY in the environment even for an X11 login session.
    if (sessionType == "x11") return false;
    if (sessionType == "wayland") return true;

    // Fall back to the display variable only when the session type is unknown.
    return qEnvironmentVariableIsSet("WAYLAND_DISPLAY");
}

static QString unsupportedWaylandMessage() {
    return "Wayland session detected: this build has no portal/EIS input backend. "
           "Use an X11 session for recording and playback; XWayland is not full Wayland support.";
}

// ---------- Helpers ----------
static MonitorInfo findMonitorForPoint(Display* dpy, int x, int y) {
    MonitorInfo result{"",0,0,0,0};
    Window root = DefaultRootWindow(dpy);
    XRRScreenResources* res = XRRGetScreenResourcesCurrent(dpy, root);
    if (!res) return result;
    for (int i = 0; i < res->noutput; ++i) {
        XRROutputInfo* output = XRRGetOutputInfo(dpy, res, res->outputs[i]);
        if (!output) continue;
        if (output->connection == RR_Connected && output->crtc) {
            XRRCrtcInfo* crtc = XRRGetCrtcInfo(dpy, res, output->crtc);
            if (crtc) {
                int w = static_cast<int>(crtc->width);
                int h = static_cast<int>(crtc->height);
                if (x >= crtc->x && x < crtc->x + w && y >= crtc->y && y < crtc->y + h) {
                    result.name = output->name;
                    result.x = crtc->x;
                    result.y = crtc->y;
                    result.width = w;
                    result.height = h;
                    XRRFreeCrtcInfo(crtc);
                    XRRFreeOutputInfo(output);
                    break;
                }
                XRRFreeCrtcInfo(crtc);
            }
        }
        XRRFreeOutputInfo(output);
    }
    XRRFreeScreenResources(res);
    return result;
}

static MonitorInfo findMonitorByName(Display* dpy, const QString& name) {
    MonitorInfo result{"",0,0,0,0};
    Window root = DefaultRootWindow(dpy);
    XRRScreenResources* res = XRRGetScreenResourcesCurrent(dpy, root);
    if (!res) return result;
    for (int i = 0; i < res->noutput; ++i) {
        XRROutputInfo* output = XRRGetOutputInfo(dpy, res, res->outputs[i]);
        if (!output) continue;
        if (output->connection == RR_Connected && output->crtc) {
            XRRCrtcInfo* crtc = XRRGetCrtcInfo(dpy, res, output->crtc);
            if (crtc) {
                if (name == output->name) {
                    result.name = output->name;
                    result.x = crtc->x;
                    result.y = crtc->y;
                    result.width = static_cast<int>(crtc->width);
                    result.height = static_cast<int>(crtc->height);
                    XRRFreeCrtcInfo(crtc);
                    XRRFreeOutputInfo(output);
                    break;
                }
                XRRFreeCrtcInfo(crtc);
            }
        }
        XRRFreeOutputInfo(output);
    }
    XRRFreeScreenResources(res);
    return result;
}

static std::int64_t now_ms() {
    timespec ts{};
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1000LL + ts.tv_nsec / 1000000LL;
}

// ---------- Config / Combos ----------
struct HotkeyCombo {
    std::vector<unsigned int> keys; // order-preserving, duplicates allowed
    QString displayName;
};
struct Config {
    QString lastDir;
    HotkeyCombo startRecording;
    HotkeyCombo startPlayback;
    HotkeyCombo stopPlayback;
};

// ---------- Recorder ----------
class RecorderThread : public QThread {
    Q_OBJECT
public:
    explicit RecorderThread(QObject *parent = nullptr) : QThread(parent) {}
    std::vector<Event> events;
    void stop() { running = false; }
signals:
    void status(const QString &s);
    void finishedRecording(const QString &summary);
protected:
    void run() override {
        running = true;
        if (isWaylandSession()) { playWayland(); return; }
        Display *dpy = XOpenDisplay(nullptr);
        if (!dpy) { emit status("Failed to open X display"); return; }
        int xi_opcode, event, error;
        if (!XQueryExtension(dpy, "XInputExtension", &xi_opcode, &event, &error)) {
            emit status("XInput2 not available"); XCloseDisplay(dpy); return;
        }
        int major = 2, minor = 0;
        if (XIQueryVersion(dpy, &major, &minor) != Success) { emit status("XInput2 < 2.0"); XCloseDisplay(dpy); return; }

        Window root = DefaultRootWindow(dpy);
        XIEventMask mask{};
        unsigned char m[32] = {0};
        mask.deviceid = XIAllMasterDevices;
        mask.mask_len = sizeof(m);
        mask.mask = m;
        XISetMask(m, XI_RawMotion);
        XISetMask(m, XI_RawButtonPress);
        XISetMask(m, XI_RawButtonRelease);
        XISetMask(m, XI_RawKeyPress);
        XISetMask(m, XI_RawKeyRelease);
        XISelectEvents(dpy, root, &mask, 1);
        XFlush(dpy);

        events.clear();
        auto start = now_ms();
        emit status("Recording...");
        int last_x = -1, last_y = -1;
        std::unordered_set<int> downButtons;

        while (running) {
            if (XPending(dpy) == 0) { std::this_thread::sleep_for(std::chrono::milliseconds(10)); continue; }
            XEvent ev; XNextEvent(dpy, &ev);
            if (ev.xcookie.type != GenericEvent || ev.xcookie.extension != xi_opcode) continue;
            if (!XGetEventData(dpy, &ev.xcookie)) continue;
            auto t = now_ms() - start;
            switch (ev.xcookie.evtype) {
                case XI_RawMotion: {
                    Window r, c; int rx, ry, x, y; unsigned int msk;
                    XQueryPointer(dpy, root, &r, &c, &rx, &ry, &x, &y, &msk);
                    if (x != last_x || y != last_y) {
                        MonitorInfo mi = findMonitorForPoint(dpy, x, y);
                        Event e; e.type = Event::MouseMove; e.ms_since_start = t; e.x = x; e.y = y;
                        e.monitor = mi.name; e.relx = x - mi.x; e.rely = y - mi.y;
                        events.push_back(e);
                        last_x = x; last_y = y;
                    }
                    break;
                }
                case XI_RawButtonPress:
                case XI_RawButtonRelease: {
                    auto *re = (XIRawEvent*)ev.xcookie.data;
                    Window r, c; int rx, ry, x, y; unsigned int msk;
                    XQueryPointer(dpy, root, &r, &c, &rx, &ry, &x, &y, &msk);
                    bool isPress = (ev.xcookie.evtype == XI_RawButtonPress);
                    if (isPress) downButtons.insert(re->detail); else downButtons.erase(re->detail);
                    MonitorInfo mi = findMonitorForPoint(dpy, x, y);
                    Event e; e.type = Event::MouseButton; e.ms_since_start = t; e.x = x; e.y = y;
                    e.button = (int)re->detail; e.pressed = isPress; e.monitor = mi.name; e.relx = x - mi.x; e.rely = y - mi.y;
                    events.push_back(e);
                    break;
                }
                case XI_RawKeyPress:
                case XI_RawKeyRelease: {
                    auto *re = (XIRawEvent*)ev.xcookie.data;
                    Event e; e.type = Event::Key; e.ms_since_start = t; e.keycode = (unsigned)re->detail;
                    e.evdevCode = re->detail >= 8 ? (unsigned)re->detail - 8 : 0;
                    e.pressed = (ev.xcookie.evtype == XI_RawKeyPress);
                    events.push_back(e);
                    break;
                }
            }
            XFreeEventData(dpy, &ev.xcookie);
        }

        if (!downButtons.empty()) {
            Window r, c; int rx, ry, x, y; unsigned int msk;
            XQueryPointer(dpy, root, &r, &c, &rx, &ry, &x, &y, &msk);
            auto t = now_ms() - start;
            MonitorInfo mi = findMonitorForPoint(dpy, x, y);
            for (int b : downButtons) {
                Event e; e.type = Event::MouseButton; e.ms_since_start = t; e.x = x; e.y = y; e.button = b; e.pressed = false;
                e.monitor = mi.name; e.relx = x - mi.x; e.rely = y - mi.y;
                events.push_back(e);
            }
        }
        XCloseDisplay(dpy);
        emit status("Stopped.");
        emit finishedRecording(QString("Recorded %1 events").arg(events.size()));
    }
private:
    std::atomic<bool> running{false};
};

// ---------- Player ----------
class PlayerThread : public QThread {
    Q_OBJECT
public:
    explicit PlayerThread(QObject *parent = nullptr) : QThread(parent) {}
    std::vector<Event> events;
    double speed = 1.0;
    int loops = 1;
    void stop() { running = false; }
signals:
    void status(const QString &s);
protected:

    bool playWayland() {
        struct oeffis *portal = oeffis_new(nullptr);
        if (!portal) {
            emit status("Could not initialize the Wayland RemoteDesktop portal.");
            return false;
        }

        emit status("Requesting Wayland input permission...");
        oeffis_create_session(portal, OEFFIS_DEVICE_KEYBOARD | OEFFIS_DEVICE_POINTER);

        int portalFd = oeffis_get_fd(portal);
        bool connected = false;
        const auto connectDeadline = now_ms() + 30000;
        while (running && now_ms() < connectDeadline && !connected) {
            pollfd pfd{portalFd, POLLIN, 0};
            int rc = poll(&pfd, 1, 100);
            if (rc > 0 && (pfd.revents & POLLIN)) {
                oeffis_dispatch(portal);
                for (;;) {
                    const auto pe = oeffis_get_event(portal);
                    if (pe == OEFFIS_EVENT_NONE) break;
                    if (pe == OEFFIS_EVENT_CONNECTED_TO_EIS) connected = true;
                    else if (pe == OEFFIS_EVENT_DISCONNECTED || pe == OEFFIS_EVENT_CLOSED) {
                        const char *why = oeffis_get_error_message(portal);
                        emit status(QString("Wayland portal closed: %1").arg(why ? why : "connection ended"));
                        oeffis_unref(portal);
                        return false;
                    }
                }
            }
        }
        if (!running || !connected) {
            emit status("Wayland input permission was not granted or the portal timed out.");
            oeffis_unref(portal);
            return false;
        }

        const int eisFd = oeffis_get_eis_fd(portal);
        if (eisFd < 0) {
            emit status("The Wayland portal did not provide an EIS connection.");
            oeffis_unref(portal);
            return false;
        }

        struct ei *ei = ei_new_sender(nullptr);
        if (!ei || ei_setup_backend_fd(ei, eisFd) != 0) {
            emit status("Could not initialize the libei Wayland input connection.");
            if (ei) ei_unref(ei);
            close(eisFd);
            oeffis_unref(portal);
            return false;
        }

        struct ei_device *pointer = nullptr;
        struct ei_device *keyboard = nullptr;
        auto dispatchEi = [&]() {
            const int fd = ei_get_fd(ei);
            pollfd pfd{fd, POLLIN, 0};
            if (fd >= 0 && poll(&pfd, 1, 0) > 0 && (pfd.revents & POLLIN))
                ei_dispatch(ei);

            for (;;) {
                struct ei_event *event = ei_get_event(ei);
                if (!event) break;
                const auto type = ei_event_get_type(event);
                if (type == EI_EVENT_SEAT_ADDED) {
                    struct ei_seat *seat = ei_event_get_seat(event);
                    if (seat) {
                        if (ei_seat_has_capability(seat, EI_DEVICE_CAP_POINTER_ABSOLUTE))
                            ei_seat_bind_capability(seat, EI_DEVICE_CAP_POINTER_ABSOLUTE);
                        else if (ei_seat_has_capability(seat, EI_DEVICE_CAP_POINTER))
                            ei_seat_bind_capability(seat, EI_DEVICE_CAP_POINTER);
                        if (ei_seat_has_capability(seat, EI_DEVICE_CAP_KEYBOARD))
                            ei_seat_bind_capability(seat, EI_DEVICE_CAP_KEYBOARD);
                    }
                } else if (type == EI_EVENT_DEVICE_RESUMED) {
                    struct ei_device *device = ei_event_get_device(event);
                    if (device) {
                        if (ei_device_has_capability(device, EI_DEVICE_CAP_POINTER_ABSOLUTE) ||
                            ei_device_has_capability(device, EI_DEVICE_CAP_POINTER)) {
                            if (pointer) ei_device_unref(pointer);
                            pointer = ei_device_ref(device);
                            ei_device_start_emulating(pointer);
                        }
                        if (ei_device_has_capability(device, EI_DEVICE_CAP_KEYBOARD)) {
                            if (keyboard) ei_device_unref(keyboard);
                            keyboard = ei_device_ref(device);
                            ei_device_start_emulating(keyboard);
                        }
                    }
                } else if (type == EI_EVENT_DEVICE_PAUSED) {
                    struct ei_device *device = ei_event_get_device(event);
                    if (device == pointer) { ei_device_unref(pointer); pointer = nullptr; }
                    if (device == keyboard) { ei_device_unref(keyboard); keyboard = nullptr; }
                } else if (type == EI_EVENT_DISCONNECT) {
                    ei_event_unref(event);
                    return false;
                }
                ei_event_unref(event);
            }
            return true;
        };

        emit status("Wayland portal connected; preparing input devices...");
        const auto deviceDeadline = now_ms() + 10000;
        while (running && now_ms() < deviceDeadline && (!pointer || !keyboard)) {
            dispatchEi();
            pollfd pfds[2] = {{ei_get_fd(ei), POLLIN, 0}, {portalFd, POLLIN, 0}};
            poll(pfds, 2, 50);
            if (pfds[0].revents & POLLIN) ei_dispatch(ei);
            if (pfds[1].revents & POLLIN) oeffis_dispatch(portal);
        }

        if (!running || !pointer || !keyboard) {
            emit status("The compositor did not provide both pointer and keyboard devices.");
            if (pointer) { ei_device_stop_emulating(pointer); ei_device_unref(pointer); }
            if (keyboard) { ei_device_stop_emulating(keyboard); ei_device_unref(keyboard); }
            ei_unref(ei);
            oeffis_unref(portal);
            return false;
        }

        auto moveAbsolute = [&](int x, int y) -> bool {
            if (!ei_device_has_capability(pointer, EI_DEVICE_CAP_POINTER_ABSOLUTE))
                return false;
            for (size_t n = 0; n < 32; ++n) {
                struct ei_region *region = ei_device_get_region(pointer, n);
                if (!region) break;
                double px = x, py = y;
                if (ei_region_contains(region, px, py) &&
                    ei_region_convert_point(region, &px, &py)) {
                    ei_device_pointer_motion_absolute(pointer, px, py);
                    ei_device_frame(pointer);
                    return true;
                }
            }
            return false;
        };

        auto linuxButton = [](int button) -> uint32_t {
            switch (button) {
                case 1: return BTN_LEFT;
                case 2: return BTN_MIDDLE;
                case 3: return BTN_RIGHT;
                case 8: return BTN_SIDE;
                case 9: return BTN_EXTRA;
                default: return 0;
            }
        };

        std::set<uint32_t> heldKeys;
        std::set<uint32_t> heldButtons;
        emit status(QString("Playing on Wayland (%1 loops, speed x%2)...").arg(loops).arg(speed));
        bool ok = true;
        for (int loop = 0; loop < loops && running && ok; ++loop) {
            const auto start = now_ms();
            for (const auto &e : events) {
                if (!running) break;
                const auto target = start + static_cast<std::int64_t>(e.ms_since_start / speed);
                while (running && now_ms() < target) {
                    dispatchEi();
                    const auto remaining = target - now_ms();
                    pollfd pfds[2] = {{ei_get_fd(ei), POLLIN, 0}, {portalFd, POLLIN, 0}};
                    poll(pfds, 2, static_cast<int>(std::min<std::int64_t>(remaining, 20)));
                    if (pfds[0].revents & POLLIN) ei_dispatch(ei);
                    if (pfds[1].revents & POLLIN) oeffis_dispatch(portal);
                }
                if (!running) break;
                if (!dispatchEi()) { ok = false; break; }

                if (e.type == Event::MouseMove) {
                    if (!moveAbsolute(e.x, e.y)) {
                        emit status("This Wayland compositor did not expose an absolute pointer region for the recorded position.");
                        ok = false;
                        break;
                    }
                } else if (e.type == Event::MouseButton) {
                    if (!moveAbsolute(e.x, e.y)) {
                        emit status("This Wayland compositor did not expose an absolute pointer region for the recorded click.");
                        ok = false;
                        break;
                    }
                    if (e.button >= 4 && e.button <= 7) {
                        if (e.pressed) {
                            const int horizontal = (e.button == 6) ? -120 : (e.button == 7 ? 120 : 0);
                            const int vertical = (e.button == 4) ? 120 : (e.button == 5 ? -120 : 0);
                            ei_device_scroll_discrete(pointer, horizontal, vertical);
                            ei_device_frame(pointer);
                        }
                        continue;
                    }
                    const uint32_t button = linuxButton(e.button);
                    if (!button) continue;
                    ei_device_button_button(pointer, button, e.pressed);
                    ei_device_frame(pointer);
                    if (e.pressed) heldButtons.insert(button); else heldButtons.erase(button);
                } else if (e.type == Event::Key) {
                    // X11 keycodes are evdev codes + 8 on Linux. New recordings
                    // persist the evdev value explicitly; old .recq files use this fallback.
                    const uint32_t code = e.evdevCode ? e.evdevCode :
                        (e.keycode >= 8 ? e.keycode - 8 : e.keycode);
                    if (code == 0) continue;
                    ei_device_keyboard_key(keyboard, code, e.pressed);
                    ei_device_frame(keyboard);
                    if (e.pressed) heldKeys.insert(code); else heldKeys.erase(code);
                }
            }
        }

        for (const auto code : heldKeys) {
            ei_device_keyboard_key(keyboard, code, false);
            ei_device_frame(keyboard);
        }
        for (const auto button : heldButtons) {
            ei_device_button_button(pointer, button, false);
            ei_device_frame(pointer);
        }
        if (pointer) { ei_device_stop_emulating(pointer); ei_device_unref(pointer); }
        if (keyboard) { ei_device_stop_emulating(keyboard); ei_device_unref(keyboard); }
        ei_unref(ei);
        oeffis_unref(portal);
        if (ok && running) emit status("Playback finished.");
        return ok;
    }

    void run() override {
        if (events.empty()) { emit status("No events to play"); return; }
        running = true;
        if (isWaylandSession()) { emit status(unsupportedWaylandMessage()); return; }
        if (!(speed > 0.0) || !std::isfinite(speed)) {
            emit status("Playback speed must be a finite value greater than zero.");
            return;
        }
        Display *dpy = XOpenDisplay(nullptr);
        if (!dpy) { emit status("Failed to open X display"); return; }
        int xtestEventBase = 0, xtestErrorBase = 0, xtestMajor = 0, xtestMinor = 0;
        if (!XTestQueryExtension(dpy, &xtestEventBase, &xtestErrorBase, &xtestMajor, &xtestMinor)) {
            emit status("XTest extension not available; playback cannot inject input.");
            XCloseDisplay(dpy);
            return;
        }
        emit status(QString("Playing (%1 loops, speed x%2)...").arg(loops).arg(speed));

        auto auto_release = [&](int button) {
            std::this_thread::sleep_for(std::chrono::milliseconds(30));
            XTestFakeButtonEvent(dpy, button, False, 0);
            XFlush(dpy);
        };

        for (int k = 0; k < loops && running; ++k) {
            auto start = now_ms();
            for (size_t i = 0; i < events.size() && running; ++i) {
                const auto &e = events[i];
                auto target = start + (std::int64_t)(e.ms_since_start / speed);
                auto n = now_ms();
                if (target > n) {
                    auto delta = target - n;
                    timespec ts{(time_t)(delta/1000), (long)((delta%1000)*1000000)};
                    nanosleep(&ts, nullptr);
                }
                switch (e.type) {
                    case Event::MouseMove: {
                        // Coordinates in .recq are absolute desktop/root coordinates.
                        // Do not remap through monitor-relative metadata: that would
                        // change the recorded location when monitor layouts change.
                        XTestFakeMotionEvent(dpy, -1, e.x, e.y, 0);
                        XFlush(dpy);
                        break;
                    }
                    case Event::MouseButton: {
                        // Restore the pointer to the exact absolute position captured
                        // with the button event before injecting the click.
                        XTestFakeMotionEvent(dpy, -1, e.x, e.y, 0);
                        XTestFakeButtonEvent(dpy, e.button, e.pressed, 0);
                        XFlush(dpy);
                        if (e.pressed) {
                            bool nextIsRelease = false;
                            if (i + 1 < events.size()) {
                                const auto &next = events[i+1];
                                nextIsRelease = (next.type == Event::MouseButton && next.button == e.button && !next.pressed);
                            }
                            if (!nextIsRelease) auto_release(e.button);
                            else std::this_thread::sleep_for(std::chrono::milliseconds(15));
                        }
                        break;
                    }
                    case Event::Key:
                        XTestFakeKeyEvent(dpy, e.keycode, e.pressed, 0);
                        XFlush(dpy);
                        break;
                }
            }
        }
        for (int b = 1; b <= 7; ++b) XTestFakeButtonEvent(dpy, b, False, 0);
        XFlush(dpy);
        XCloseDisplay(dpy);
        emit status("Playback finished.");
    }
private:
    std::atomic<bool> running{false};
};

// ---------- Global key watcher (for triggering combos while app unfocused) ----------
class GlobalKeyWatcher : public QThread {
    Q_OBJECT
public:
    explicit GlobalKeyWatcher(QObject *parent = nullptr) : QThread(parent) {}
    void stop() { running = false; }
signals:
    void currentDownSetChanged(const std::vector<unsigned int>& downSet);
protected:
    void run() override {
        running = true;
        if (isWaylandSession()) return;
        Display *dpy = XOpenDisplay(nullptr);
        if (!dpy) return;
        int xi_opcode, event, error;
        if (!XQueryExtension(dpy, "XInputExtension", &xi_opcode, &event, &error)) { XCloseDisplay(dpy); return; }
        int major = 2, minor = 0;
        if (XIQueryVersion(dpy, &major, &minor) != Success) { XCloseDisplay(dpy); return; }
        Window root = DefaultRootWindow(dpy);
        XIEventMask mask{}; unsigned char m[32] = {0}; mask.deviceid = XIAllMasterDevices; mask.mask_len = sizeof(m); mask.mask = m;
        XISetMask(m, XI_RawKeyPress); XISetMask(m, XI_RawKeyRelease); XISelectEvents(dpy, root, &mask, 1); XFlush(dpy);

        std::vector<unsigned int> downOrder; // track order and allow duplicates? For triggering, we compare orderless trimmed sets
        std::set<unsigned int> downSet;

        while (running) {
            if (XPending(dpy) == 0) { std::this_thread::sleep_for(std::chrono::milliseconds(10)); continue; }
            XEvent ev; XNextEvent(dpy, &ev);
            if (ev.xcookie.type == GenericEvent && ev.xcookie.extension == xi_opcode) {
                if (XGetEventData(dpy, &ev.xcookie)) {
                    if (ev.xcookie.evtype == XI_RawKeyPress) {
                        auto *re = (XIRawEvent*)ev.xcookie.data;
                        unsigned int code = (unsigned)re->detail;
                        downSet.insert(code);
                        // emit current set (sorted)
                        std::vector<unsigned int> v(downSet.begin(), downSet.end());
                        emit currentDownSetChanged(v);
                    } else if (ev.xcookie.evtype == XI_RawKeyRelease) {
                        auto *re = (XIRawEvent*)ev.xcookie.data;
                        unsigned int code = (unsigned)re->detail;
                        downSet.erase(code);
                        std::vector<unsigned int> v(downSet.begin(), downSet.end());
                        emit currentDownSetChanged(v);
                    }
                    XFreeEventData(dpy, &ev.xcookie);
                }
            }
        }
        XCloseDisplay(dpy);
    }
private:
    std::atomic<bool> running{false};
};

// ---------- Helper: friendly key names (uses XKB) ----------
static const std::map<QString, QString> friendlyMap = {
    {"Shift_L","Shift"}, {"Shift_R","Shift"}, {"Control_L","Ctrl"}, {"Control_R","Ctrl"},
    {"Alt_L","Alt"}, {"Alt_R","Alt"}, {"Super_L","Super"}, {"Super_R","Super"},
    {"ISO_Level3_Shift","AltGr"}, {"Meta_L","Meta"}, {"Meta_R","Meta"},
    {"Return","Enter"}, {"BackSpace","Backspace"}, {"Escape","Esc"}, {"space","Space"}, {"Tab","Tab"},
    {"Left","Left"}, {"Right","Right"}, {"Up","Up"}, {"Down","Down"},
    {"Prior","PgUp"}, {"Next","PgDn"}, {"Home","Home"}, {"End","End"},
    {"Insert","Ins"}, {"Delete","Del"}
};

static QString friendlyKeyName(const char* ksname) {
    if (!ksname) return QString();
    QString s = QString::fromUtf8(ksname);
    auto it = friendlyMap.find(s);
    if (it != friendlyMap.end()) return it->second;
    if (s.endsWith("_L") || s.endsWith("_R")) {
        QString base = s.left(s.size()-2);
        auto it2 = friendlyMap.find(base);
        if (it2 != friendlyMap.end()) return it2->second;
        return base;
    }
    return s;
}

// Use XKB state heuristics to pick the most likely keysym (so Shift gives upper-case, etc.)
static QString keycodeToString(Display* dpy, unsigned int keycode) {
    bool opened = false;
    if (!dpy) { dpy = XOpenDisplay(nullptr); opened = true; if (!dpy) return QString("Key%1").arg(keycode); }
    XkbStateRec state;
    int level = 0, group = 0;
    if (XkbGetState(dpy, XkbUseCoreKbd, &state) == Success) {
        group = state.group & 0xFF;
        if (state.mods & ShiftMask) level = 1;
        if (state.mods & Mod5Mask) level = 2;
        if (level < 0) level = 0;
        if (level > 3) level = 3;
    }
    KeySym ks = XkbKeycodeToKeysym(dpy, (KeyCode)keycode, group, level);
    if (ks == NoSymbol) {
        for (int lv = 0; lv <= 2 && ks == NoSymbol; ++lv) ks = XkbKeycodeToKeysym(dpy, (KeyCode)keycode, group, lv);
    }
    const char *name = XKeysymToString(ks);
    QString out = friendlyKeyName(name);
    if (out.isEmpty()) out = QString("Key%1").arg(keycode);
    if (opened) XCloseDisplay(dpy);
    return out;
}

static QString comboToDisplay(const std::vector<unsigned int>& keys) {
    if (keys.empty()) return "None";
    Display *dpy = XOpenDisplay(nullptr);
    QStringList parts;
    for (auto k : keys) parts << keycodeToString(dpy, k);
    if (dpy) XCloseDisplay(dpy);
    return parts.join(" + ");
}

// ---------- Capture worker: listens for raw key presses while dialog is open ----------
class CaptureWorker : public QObject {
    Q_OBJECT
public:
    CaptureWorker(QObject *parent = nullptr) : QObject(parent) {}
    void stop() { running = false; }
signals:
    void capturedKey(unsigned int keycode); // emits each key press
    void finished(); // emitted when worker stops
public slots:
    void run() {
        running = true;
        if (isWaylandSession()) { emit finished(); return; }
        Display *dpy = XOpenDisplay(nullptr);
        if (!dpy) { emit finished(); return; }
        int xi_opcode, event, error;
        if (!XQueryExtension(dpy, "XInputExtension", &xi_opcode, &event, &error)) { XCloseDisplay(dpy); emit finished(); return; }
        int major = 2, minor = 0;
        if (XIQueryVersion(dpy, &major, &minor) != Success) { XCloseDisplay(dpy); emit finished(); return; }

        Window root = DefaultRootWindow(dpy);
        XIEventMask mask{}; unsigned char m[32] = {0};
        mask.deviceid = XIAllMasterDevices;
        mask.mask_len = sizeof(m);
        mask.mask = m;
        XISetMask(m, XI_RawKeyPress);
        XISelectEvents(dpy, root, &mask, 1);
        XFlush(dpy);

        while (running) {
            if (XPending(dpy) == 0) { std::this_thread::sleep_for(std::chrono::milliseconds(10)); continue; }
            XEvent ev; XNextEvent(dpy, &ev);
            if (ev.xcookie.type == GenericEvent && ev.xcookie.extension == xi_opcode) {
                if (XGetEventData(dpy, &ev.xcookie)) {
                    if (ev.xcookie.evtype == XI_RawKeyPress) {
                        auto *re = (XIRawEvent*)ev.xcookie.data;
                        unsigned int code = (unsigned)re->detail;
                        emit capturedKey(code);
                    }
                    XFreeEventData(dpy, &ev.xcookie);
                }
            }
        }
        XCloseDisplay(dpy);
        emit finished();
    }
private:
    std::atomic<bool> running{false};
};

// ---------- MainWindow ----------
class MainWindow : public QMainWindow {
    Q_OBJECT
public:
    explicit MainWindow(QWidget *parent = nullptr) : QMainWindow(parent) {
        keyWatcher = new GlobalKeyWatcher(this);
        loadConfig();
        setupUi();

        connect(keyWatcher, &GlobalKeyWatcher::currentDownSetChanged, this, [this](const std::vector<unsigned int>& downset){
            // convert down-set to orderless sorted set for comparison with saved combos
            std::vector<unsigned int> s = downset;
            std::sort(s.begin(), s.end());
            // Compare against each configured combo, trimming trailing placeholders isn't needed here because saved combos are trimmed
            if (!config.startRecording.keys.empty()) {
                std::vector<unsigned int> saved = config.startRecording.keys;
                std::vector<unsigned int> savedSorted = saved; std::sort(savedSorted.begin(), savedSorted.end());
                if (savedSorted == s) QMetaObject::invokeMethod(this, "onToggleRecord", Qt::QueuedConnection);
            }
            if (!config.startPlayback.keys.empty()) {
                std::vector<unsigned int> saved = config.startPlayback.keys;
                std::vector<unsigned int> savedSorted = saved; std::sort(savedSorted.begin(), savedSorted.end());
                if (savedSorted == s) QMetaObject::invokeMethod(this, "onTogglePlay", Qt::QueuedConnection);
            }
            if (!config.stopPlayback.keys.empty()) {
                std::vector<unsigned int> saved = config.stopPlayback.keys;
                std::vector<unsigned int> savedSorted = saved; std::sort(savedSorted.begin(), savedSorted.end());
                if (savedSorted == s) QMetaObject::invokeMethod(this, "onStopPlaybackHotkey", Qt::QueuedConnection);
            }
        });

        keyWatcher->start();
    }

    ~MainWindow() override {
        if (activeRecorder) { activeRecorder->stop(); activeRecorder->wait(); activeRecorder->deleteLater(); activeRecorder = nullptr; }
        if (activePlayer) { activePlayer->stop(); activePlayer->wait(); activePlayer->deleteLater(); activePlayer = nullptr; }
        if (keyWatcher) { keyWatcher->stop(); keyWatcher->wait(); }
        saveConfig();
    }

private:
    RecorderThread *activeRecorder{nullptr};
    PlayerThread *activePlayer{nullptr};
    GlobalKeyWatcher *keyWatcher{nullptr};

    std::vector<Event> recorded;
    QLabel *status{nullptr};
    QDoubleSpinBox *spinSpeed{nullptr};
    QSpinBox *spinLoops{nullptr};
    QCheckBox *chkInfinite{nullptr};
    QPushButton *btnRecord{nullptr};
    QPushButton *btnPlay{nullptr};
    QPushButton *btnSave{nullptr};
    QPushButton *btnLoad{nullptr};
    QPushButton *btnHotkey{nullptr};

    Config config;

    QString configFilePath() const {
        QString dir = QStandardPaths::writableLocation(QStandardPaths::AppConfigLocation);
        if (dir.isEmpty()) dir = QDir::homePath() + "/.config/BiggerTask";
        QDir d(dir); if (!d.exists()) d.mkpath("."); return d.filePath("config.json");
    }

    void loadConfig() {
        QString path = configFilePath();
        QFile f(path);
        if (!f.exists()) {
            config.lastDir = QDir::homePath();
            config.startRecording = HotkeyCombo{{}, ""};
            config.startPlayback = HotkeyCombo{{}, ""};
            config.stopPlayback = HotkeyCombo{{}, ""};
            return;
        }
        if (!f.open(QIODevice::ReadOnly)) return;
        auto doc = QJsonDocument::fromJson(f.readAll()); f.close();
        if (!doc.isObject()) return;
        auto root = doc.object();
        config.lastDir = root.value("lastDir").toString(QDir::homePath());
        auto loadCombo = [](const QJsonObject &o)->HotkeyCombo {
            HotkeyCombo c;
            c.displayName = o.value("display").toString();
            auto arr = o.value("keys").toArray();
            for (auto v : arr) c.keys.push_back((unsigned int)v.toInt());
            return c;
        };
        config.startRecording = loadCombo(root.value("startRecording").toObject());
        config.startPlayback = loadCombo(root.value("startPlayback").toObject());
        config.stopPlayback = loadCombo(root.value("stopPlayback").toObject());
    }

    void saveConfig() {
        QJsonObject root;
        root["lastDir"] = config.lastDir;
        auto saveCombo = [](const HotkeyCombo &c)->QJsonObject {
            QJsonObject o; o["display"] = c.displayName;
            QJsonArray a; for (auto k : c.keys) a.append((int)k);
            o["keys"] = a; return o;
        };
        root["startRecording"] = saveCombo(config.startRecording);
        root["startPlayback"] = saveCombo(config.startPlayback);
        root["stopPlayback"] = saveCombo(config.stopPlayback);
        QJsonDocument doc(root);
        QFile f(configFilePath()); if (!f.open(QIODevice::WriteOnly)) return; f.write(doc.toJson(QJsonDocument::Compact)); f.close();
    }

    void setupUi() {
        auto *central = new QWidget(this);
        auto *v = new QVBoxLayout(central);

        auto *h1 = new QHBoxLayout();
        btnRecord = new QPushButton("Record");
        btnPlay = new QPushButton("Play");
        btnSave = new QPushButton("Save");
        btnLoad = new QPushButton("Load");
        btnHotkey = new QPushButton("Hotkeys");
        h1->addWidget(btnRecord); h1->addWidget(btnPlay); h1->addWidget(btnSave); h1->addWidget(btnLoad); h1->addWidget(btnHotkey);

        auto *h2 = new QHBoxLayout();
        spinSpeed = new QDoubleSpinBox(); spinSpeed->setRange(0.1, 5.0); spinSpeed->setValue(1.0);
        spinLoops = new QSpinBox(); spinLoops->setRange(1, 999); spinLoops->setValue(1);
        chkInfinite = new QCheckBox("Infinite loop");
        h2->addWidget(new QLabel("Speed:")); h2->addWidget(spinSpeed); h2->addWidget(new QLabel("Loops:")); h2->addWidget(spinLoops); h2->addWidget(chkInfinite);

        status = new QLabel("Ready.");

        v->addLayout(h1);
        v->addLayout(h2);
        v->addWidget(status);
        setCentralWidget(central);

        btnPlay->setEnabled(false);
        btnSave->setEnabled(false);

        // Record button
        connect(btnRecord, &QPushButton::clicked, this, &MainWindow::onToggleRecord);
        // Play button
        connect(btnPlay, &QPushButton::clicked, this, &MainWindow::onTogglePlay);

        // Save
        connect(btnSave, &QPushButton::clicked, this, [this]() {
            if (recorded.empty()) return;
            QString startDir = config.lastDir.isEmpty() ? QDir::homePath() : config.lastDir;
            QString path = QFileDialog::getSaveFileName(this, "Save macro", startDir, "Macro (*.recq)");
            if (path.isEmpty()) return;
            if (!path.endsWith(".recq")) path += ".recq";
            if (saveRecq(path, recorded)) { QFileInfo fi(path); config.lastDir = fi.absolutePath(); saveConfig(); }
            else QMessageBox::warning(this, "Save failed", "Failed to save file.");
        });

        // Load
        connect(btnLoad, &QPushButton::clicked, this, [this]() {
            QString startDir = config.lastDir.isEmpty() ? QDir::homePath() : config.lastDir;
            QString path = QFileDialog::getOpenFileName(this, "Load macro", startDir, "Macro (*.recq)");
            if (path.isEmpty()) return;
            recorded = loadRecq(path);
            if (!recorded.empty()) { QFileInfo fi(path); config.lastDir = fi.absolutePath(); saveConfig(); }
            btnPlay->setEnabled(!recorded.empty()); btnSave->setEnabled(!recorded.empty());
            status->setText(QString("Loaded %1 events").arg(recorded.size()));
        });

        // Hotkeys menu (capture or clear)
        connect(btnHotkey, &QPushButton::clicked, this, [this]() {
            QMenu menu;
            QAction *a1 = menu.addAction(QString("Set Start Recording (current: %1)").arg(config.startRecording.displayName.isEmpty() ? "None" : config.startRecording.displayName));
            QAction *a2 = menu.addAction(QString("Set Start Playback (current: %1)").arg(config.startPlayback.displayName.isEmpty() ? "None" : config.startPlayback.displayName));
            QAction *a3 = menu.addAction(QString("Set Stop Playback (current: %1)").arg(config.stopPlayback.displayName.isEmpty() ? "None" : config.stopPlayback.displayName));
            menu.addSeparator();
            QAction *a4 = menu.addAction("Clear Start Recording");
            QAction *a5 = menu.addAction("Clear Start Playback");
            QAction *a6 = menu.addAction("Clear Stop Playback");
            QAction *sel = menu.exec(btnHotkey->mapToGlobal(btnHotkey->rect().bottomLeft()));
            if (!sel) return;
            if (sel == a1) openCaptureDialog(&config.startRecording);
            else if (sel == a2) openCaptureDialog(&config.startPlayback);
            else if (sel == a3) openCaptureDialog(&config.stopPlayback);
            else if (sel == a4) { config.startRecording.keys.clear(); config.startRecording.displayName = ""; saveConfig(); }
            else if (sel == a5) { config.startPlayback.keys.clear(); config.startPlayback.displayName = ""; saveConfig(); }
            else if (sel == a6) { config.stopPlayback.keys.clear(); config.stopPlayback.displayName = ""; saveConfig(); }
        });
    }

    Q_SLOT void onToggleRecord() {
        if (!activeRecorder) {
            activeRecorder = new RecorderThread(this);
            connect(activeRecorder, &RecorderThread::status, this, [this](const QString &s){ status->setText(s); });
            connect(activeRecorder, &RecorderThread::finishedRecording, this, [this](const QString &summary){
                status->setText(summary);
                recorded = activeRecorder->events;
            });
            // QThread::finished also fires on early backend errors (including the
            // intentionally unsupported Wayland path), so the controls never stick.
            connect(activeRecorder, &QThread::finished, this, [this]() {
                btnRecord->setText("Record");
                btnPlay->setEnabled(!recorded.empty());
                btnSave->setEnabled(!recorded.empty());
                if (activeRecorder) {
                    activeRecorder->deleteLater();
                    activeRecorder = nullptr;
                }
            });
            activeRecorder->start();
            btnRecord->setText("Stop");
            btnPlay->setEnabled(false);
            btnSave->setEnabled(false);
        } else {
            activeRecorder->stop();
            btnRecord->setText("Record");
        }
    }

    Q_SLOT void onTogglePlay() {
    if (activePlayer) {
        // Already playing — ignore Start Playback hotkey
        return;
    }

    if (!recorded.empty()) {
        activePlayer = new PlayerThread(this);
        activePlayer->events = recorded;
        activePlayer->speed = spinSpeed->value();
        activePlayer->loops = chkInfinite->isChecked() ? INT_MAX : spinLoops->value();

        connect(activePlayer, &PlayerThread::status, this, [this](const QString &s){
            status->setText(s);
        });
        // Handle normal completion, stop, and backend startup failures uniformly.
        connect(activePlayer, &QThread::finished, this, [this]() {
            btnPlay->setText("Play");
            btnRecord->setEnabled(true);
            if (activePlayer) {
                activePlayer->deleteLater();
                activePlayer = nullptr;
            }
        });

        activePlayer->start();
        btnPlay->setText("Stop");
        btnRecord->setEnabled(false);
    }
}

    Q_SLOT void onStopPlaybackHotkey() {
        if (activePlayer) activePlayer->stop();
    }

    // Modal capture dialog implementation
    void openCaptureDialog(HotkeyCombo *target) {
    QDialog dlg(this);
    dlg.setWindowTitle("Capture hotkey combo (up to 3 unique keys)");
    QVBoxLayout *lay = new QVBoxLayout(&dlg);
    QLabel *info = new QLabel("Press up to 3 unique keys.\nReset clears slots. Save trims trailing empty slots.");
    lay->addWidget(info);

    QHBoxLayout *h = new QHBoxLayout();
    QLabel *slotLbls[3];
    for (int i = 0; i < 3; ++i) {
        slotLbls[i] = new QLabel("None");
        slotLbls[i]->setMinimumWidth(80);
        slotLbls[i]->setAlignment(Qt::AlignCenter);
        h->addWidget(slotLbls[i]);
        if (i < 2) {
            QLabel *plus = new QLabel(" + ");
            plus->setAlignment(Qt::AlignCenter);
            h->addWidget(plus);
        }
    }
    lay->addLayout(h);

    QHBoxLayout *btnLine = new QHBoxLayout();
    QPushButton *btnReset = new QPushButton("Reset");
    QPushButton *btnSave = new QPushButton("Save");
    QPushButton *btnCancel = new QPushButton("Cancel");
    btnLine->addWidget(btnReset);
    btnLine->addWidget(btnSave);
    btnLine->addWidget(btnCancel);
    lay->addLayout(btnLine);

    std::vector<unsigned int> seq = target->keys;
    for (int i = 0; i < 3; ++i) {
        if (i < (int)seq.size()) slotLbls[i]->setText(keycodeToString(nullptr, seq[i]));
        else slotLbls[i]->setText("None");
    }

    QThread *workerThread = new QThread;
    CaptureWorker *worker = new CaptureWorker();
    worker->moveToThread(workerThread);

    bool useTimeout = (target != &config.startRecording);
    QTimer *comboTimer = nullptr;
    if (useTimeout) {
        comboTimer = new QTimer(&dlg);
        comboTimer->setInterval(1000);
        comboTimer->setSingleShot(true);
        connect(comboTimer, &QTimer::timeout, &dlg, [&]() {
            worker->stop();
        });
    }

    connect(workerThread, &QThread::started, worker, &CaptureWorker::run);
    connect(worker, &CaptureWorker::capturedKey, &dlg, [&](unsigned int keycode) {
        if (std::find(seq.begin(), seq.end(), keycode) != seq.end()) return; // skip duplicates
        if ((int)seq.size() < 3) {
            seq.push_back(keycode);
            int idx = seq.size() - 1;
            slotLbls[idx]->setText(keycodeToString(nullptr, keycode));
            if (useTimeout && comboTimer) comboTimer->start();
        }
    }, Qt::QueuedConnection);

    connect(btnReset, &QPushButton::clicked, &dlg, [&]() {
        seq.clear();
        for (int i = 0; i < 3; ++i) slotLbls[i]->setText("None");
        if (useTimeout && comboTimer) comboTimer->stop();
    });

    connect(btnCancel, &QPushButton::clicked, &dlg, [&]() {
        worker->stop();
        dlg.reject();
    });

    connect(btnSave, &QPushButton::clicked, &dlg, [&]() {
        target->keys = seq;
        target->displayName = seq.empty() ? "None" : comboToDisplay(seq);
        saveConfig();
        worker->stop();
        dlg.accept();
    });

if (seq.size() >= 3) {
    seq.clear();
    for (int i = 0; i < 3; ++i) slotLbls[i]->setText("None");
}

    workerThread->start();
    if (useTimeout && comboTimer) comboTimer->start();
    dlg.exec();
    worker->stop();
    workerThread->quit();
    workerThread->wait();
    delete worker;
    delete workerThread;
}


    // Save/load .recq (unchanged)
    static bool saveRecq(const QString &path, const std::vector<Event> &evs) {
        QJsonArray arr;
        for (const auto &e : evs) {
            QJsonObject o; o["t"] = (double)e.ms_since_start;
            if (e.type == Event::MouseMove) { o["type"]="mm"; o["x"]=e.x; o["y"]=e.y; }
            else if (e.type == Event::MouseButton) { o["type"]="mb"; o["x"]=e.x; o["y"]=e.y; o["btn"]=e.button; o["down"]=e.pressed; }
            else { o["type"]="key"; o["code"]=(int)e.keycode; o["down"]=e.pressed; }
            // Optional v1 extensions: old readers ignore these fields; new readers
            // can restore monitor-relative absolute coordinates on multi-monitor setups.
            if (e.evdevCode) o["evdevCode"] = static_cast<int>(e.evdevCode);
            if (!e.monitor.isEmpty()) {
                o["monitor"] = e.monitor;
                o["relx"] = e.relx;
                o["rely"] = e.rely;
            }
            arr.append(o);
        }
        QJsonObject root; root["format"]="recq-v1"; root["events"]=arr;
        QJsonDocument doc(root); QFile f(path); if (!f.open(QIODevice::WriteOnly)) return false; f.write(doc.toJson(QJsonDocument::Compact)); f.close(); return true;
    }

    static std::vector<Event> loadRecq(const QString &path) {
        std::vector<Event> out; QFile f(path); if (!f.open(QIODevice::ReadOnly)) return out; auto data = f.readAll(); f.close();
        auto doc = QJsonDocument::fromJson(data);
        if (doc.isObject()) {
            auto root = doc.object(); auto arr = root.value("events").toArray();
            for (auto v : arr) {
                auto o = v.toObject(); Event e{}; e.ms_since_start = (std::int64_t)o.value("t").toDouble(); auto type = o.value("type").toString();
                if (type=="mm") { e.type=Event::MouseMove; e.x=o.value("x").toInt(); e.y=o.value("y").toInt(); }
                else if (type=="mb") { e.type=Event::MouseButton; e.x=o.value("x").toInt(); e.y=o.value("y").toInt(); e.button=o.value("btn").toInt(); e.pressed=o.value("down").toBool(); }
                else if (type=="key") { e.type=Event::Key; e.keycode=o.value("code").toInt(); e.pressed=o.value("down").toBool(); }
                e.evdevCode = static_cast<unsigned int>(o.value("evdevCode").toInt());
                e.evdevCode = static_cast<unsigned int>(o.value("evdevCode").toInt());
                e.monitor = o.value("monitor").toString();
                e.relx = o.value("relx").toInt();
                e.rely = o.value("rely").toInt();
                out.push_back(e);
            }
        } else if (doc.isArray()) {
            for (auto v : doc.array()) {
                auto o = v.toObject(); Event e{}; e.ms_since_start = (std::int64_t)o.value("t").toDouble(); auto type = o.value("type").toString();
                if (type=="mm") { e.type=Event::MouseMove; e.x=o.value("x").toInt(); e.y=o.value("y").toInt(); }
                else if (type=="mb") { e.type=Event::MouseButton; e.x=o.value("x").toInt(); e.y=o.value("y").toInt(); e.button=o.value("btn").toInt(); e.pressed=o.value("down").toBool(); }
                else if (type=="key") { e.type=Event::Key; e.keycode=o.value("code").toInt(); e.pressed=o.value("down").toBool(); }
                e.monitor = o.value("monitor").toString();
                e.relx = o.value("relx").toInt();
                e.rely = o.value("rely").toInt();
                out.push_back(e);
            }
        }
        return out;
    }

signals:
    void liveCaptureUpdate(const std::vector<unsigned int>& down); // unused here but kept for compatibility

}; // end MainWindow

// ---------- main ----------


int main(int argc, char *argv[]) {
    qRegisterMetaType<std::vector<unsigned int>>("std::vector<unsigned int>");
    QApplication app(argc, argv);
    app.setWindowIcon(QIcon(":/icons/BiggerTask.svg"));
    MainWindow w;
    w.setWindowTitle("BiggerTask");
    w.show();
    return app.exec();
}

#include "BiggerTask.moc"
