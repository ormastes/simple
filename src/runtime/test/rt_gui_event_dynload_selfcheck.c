#include "runtime.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <dlfcn.h>
#include <pthread.h>

static int fail_alloc;
void *gui_test_malloc(size_t size) { return fail_alloc ? NULL : malloc(size); }
static pthread_mutex_t hold_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t hold_condition = PTHREAD_COND_INITIALIZER;
static int present_held;
void simple_gui_test_present_hold(void) {
    pthread_mutex_lock(&hold_lock);
    present_held = 1;
    pthread_cond_broadcast(&hold_condition);
    for (;;) pthread_cond_wait(&hold_condition, &hold_lock);
}

static void *off_thread(void *operation) {
    const char *name = operation;
    if (!strcmp(name, "thread-open")) rt_gui_begin_session();
    if (!strcmp(name, "thread-poll")) (void)rt_gui_poll_event();
    if (!strcmp(name, "thread-present"))
        rt_gui_session_present_html(rt_string_new((const uint8_t *)"<p>ok</p>", 9));
    if (!strcmp(name, "thread-close")) rt_gui_end_session();
    if (!strcmp(name, "thread-standalone") || !strcmp(name, "open-overlap"))
        rt_gui_present_html(rt_string_new((const uint8_t *)"<p>ok</p>", 9));
    abort();
}
static void worker(const char *operation) {
    pthread_t thread;
    assert(!pthread_create(&thread, NULL, off_thread, (void *)operation));
    assert(!pthread_join(thread, NULL));
}
static void expect_event(const char *expected) {
    int64_t event = rt_gui_poll_event();
    assert(rt_string_len(event) == (int64_t)strlen(expected));
    assert(!memcmp(rt_string_data(event), expected, strlen(expected)));
}

int main(int argc, char **argv) {
    const char *mode = argc > 1 ? argv[1] : "normal";
    if (!strcmp(mode, "headless")) {
        assert(!dlopen(getenv("SIMPLE_GUI_HTML_PROVIDER_PATH"), RTLD_NOW | RTLD_NOLOAD));
        return 0;
    }
    if (!strcmp(mode, "thread-open")) worker(mode);
    if (!strcmp(mode, "inactive-poll")) (void)rt_gui_poll_event();
    if (!strcmp(mode, "inactive-close")) rt_gui_end_session();
    if (!strcmp(mode, "inactive-present")) rt_gui_session_present_html(3);
    if (!strcmp(mode, "open-overlap")) {
        pthread_t thread;
        assert(!pthread_create(&thread, NULL, off_thread, (void *)mode));
        pthread_mutex_lock(&hold_lock);
        while (!present_held) pthread_cond_wait(&hold_condition, &hold_lock);
        pthread_mutex_unlock(&hold_lock);
    }
    if (!strcmp(mode, "standalone-before-session"))
        rt_gui_present_html(rt_string_new((const uint8_t *)"<p>ok</p>", 9));
    rt_gui_begin_session();
    if (!strcmp(mode, "standalone-overlap"))
        rt_gui_present_html(rt_string_new((const uint8_t *)"<p>ok</p>", 9));
    if (!strcmp(mode, "nested")) rt_gui_begin_session();
    if (!strncmp(mode, "thread-", 7)) worker(mode);
    rt_gui_session_present_html(rt_string_new((const uint8_t *)"<p>ok</p>", 9));
    if (!strncmp(mode, "alloc-", 6)) fail_alloc = 1;
    if (!strcmp(mode, "unicode")) {
        expect_event("text\n한\n🙂");
        rt_gui_end_session();
        return 0;
    }
    if (!strcmp(mode, "max-packet")) {
        int64_t event = rt_gui_poll_event();
        assert(rt_string_len(event) == 4096);
        assert(rt_string_data(event)[4095] == 'x');
        rt_gui_end_session();
        return 0;
    }
    int64_t retained_event = rt_gui_poll_event();
    assert(rt_string_len(retained_event) == 12);
    assert(!memcmp(rt_string_data(retained_event), "text\nhello\nx", 12));
    expect_event("key\nCtrl+s");
    expect_event("focus\n");
    expect_event("mouse-down\n7,9");
    expect_event("mouse-move\n8,10");
    expect_event("mouse-up\n");
    expect_event("resize\n800,600");
    expect_event("blur\n");
    int64_t idle = rt_gui_poll_event();
    assert(rt_string_len(idle) == 0);
    assert(rt_gui_poll_event() == idle);
    expect_event("close\n");
    rt_gui_end_session();
    assert(rt_string_len(retained_event) == 12);
    assert(!memcmp(rt_string_data(retained_event), "text\nhello\nx", 12));
    if (!strcmp(mode, "double-close")) rt_gui_end_session();
    rt_gui_begin_session();
    rt_gui_session_present_html(rt_string_new((const uint8_t *)"<p>ok</p>", 9));
    expect_event("text\nhello\nx");
    rt_gui_end_session();
    void *library = dlopen(getenv("SIMPLE_GUI_HTML_PROVIDER_PATH"), RTLD_NOW | RTLD_NOLOAD);
    assert(library);
    union { void *symbol; int64_t (*call)(void); } counts;
    counts.symbol = dlsym(library, "simple_gui_event_test_counts");
    int64_t expected = !strcmp(mode, "standalone-before-session") ? 1131202 : 1121202;
    assert(counts.call && counts.call() == expected);
    dlclose(library);
    puts("GUI event lifecycle PASS");
    return 0;
}
