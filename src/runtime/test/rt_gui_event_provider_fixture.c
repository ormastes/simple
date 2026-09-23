#include "simple_gui_html_provider_abi_v1.h"
#include "simple_gui_event_provider_abi_v1.h"
#include <assert.h>
#include <dlfcn.h>
#include <stdlib.h>
#include <string.h>

static int html_versions, event_versions, presents, polls, shutdowns, sequence;
static const char *mode(void) {
    const char *value = getenv("SIMPLE_GUI_EVENT_TEST_MODE");
    return value ? value : "normal";
}
static void reenter(void) {
    union { void *symbol; void (*call)(void); } begin;
    begin.symbol = dlsym(RTLD_DEFAULT, "rt_gui_begin_session");
    assert(begin.call);
    begin.call();
    abort();
}
int64_t simple_gui_html_provider_abi_v1(void) {
    html_versions++;
    if (!strcmp(mode(), "html-reentry")) reenter();
    return 1;
}
int64_t simple_gui_present_html_v1(const uint8_t *bytes, uint64_t length) {
    assert(length == 9 && !memcmp(bytes, "<p>ok</p>", 9));
    presents++;
    if (!strcmp(mode(), "open-overlap")) {
        union { void *symbol; void (*call)(void); } hold;
        hold.symbol = dlsym(RTLD_DEFAULT, "simple_gui_test_present_hold");
        assert(hold.call);
        hold.call();
    }
    if (!strcmp(mode(), "present-reentry")) reenter();
    return !strcmp(mode(), "present-reject") ? 0 : 1;
}
int64_t simple_gui_event_provider_abi_v1(void) {
    event_versions++;
    if (!strcmp(mode(), "version-reentry")) reenter();
    return !strcmp(mode(), "bad-version") ? 2 : 1;
}
int64_t simple_gui_poll_event_v1(uint8_t *bytes, uint64_t capacity, uint64_t wait_ms) {
    assert(capacity == 4096 && wait_ms == 16);
    polls++;
    if (!strcmp(mode(), "poll-reentry")) reenter();
    if (!strcmp(mode(), "poll-reject")) return -1;
    if (!strcmp(mode(), "alloc-idle")) return 0;
    if (!strcmp(mode(), "unicode")) {
        const char *text = "text\n한\n🙂";
        memcpy(bytes, text, strlen(text));
        return (int64_t)strlen(text);
    }
    if (!strcmp(mode(), "overflow")) return 4097;
    if (!strcmp(mode(), "unwritten")) return 6;
    if (!strcmp(mode(), "no-delimiter")) { memcpy(bytes, "close", 5); return 5; }
    if (!strcmp(mode(), "empty-kind")) { memcpy(bytes, "\nx", 2); return 2; }
    if (!strcmp(mode(), "invalid-kind")) { memcpy(bytes, "TEXT\nx", 6); return 6; }
    if (!strcmp(mode(), "long-kind")) { memset(bytes, 'a', 32); bytes[32] = '\n'; return 33; }
    if (!strcmp(mode(), "nul")) { memcpy(bytes, "text\n\0x", 7); return 7; }
    if (!strcmp(mode(), "utf8")) { memcpy(bytes, "text\n\xff", 6); return 6; }
    if (!strcmp(mode(), "max-packet")) {
        memcpy(bytes, "text\n", 5);
        memset(bytes + 5, 'x', capacity - 5);
        return (int64_t)capacity;
    }
    static const char *events[] = {
        "text\nhello\nx", "key\nCtrl+s", "focus\n", "mouse-down\n7,9",
        "mouse-move\n8,10", "mouse-up\n", "resize\n800,600", "blur\n", "", "", "close\n"
    };
    assert(sequence < (int)(sizeof(events) / sizeof(events[0])));
    const char *event = events[sequence++];
    size_t length = strlen(event);
    memcpy(bytes, event, length);
    return (int64_t)length;
}
#if !defined(SIMPLE_GUI_EVENT_TEST_NO_SHUTDOWN)
int64_t simple_gui_shutdown_v1(void) {
    shutdowns++;
    sequence = 0;
    if (!strcmp(mode(), "shutdown-reentry")) reenter();
    return !strcmp(mode(), "shutdown-reject") ? 0 : 1;
}
#endif
int64_t simple_gui_event_test_counts(void) {
    return html_versions * 1000000 + event_versions * 100000 + presents * 10000 +
           polls * 100 + shutdowns;
}
