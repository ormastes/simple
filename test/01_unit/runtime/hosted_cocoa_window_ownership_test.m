/* Real AppKit/MRC lifecycle regression; run in a macOS GUI login session.
 * clang -fno-objc-arc -framework Cocoa -Werror \
 *   test/01_unit/runtime/hosted_cocoa_window_ownership_test.m -o /tmp/cocoa-window
 * /tmp/cocoa-window [normal|record-failure|table-full|window-failure|view-failure|user-close|thread]
 */
#import <Cocoa/Cocoa.h>
#include <assert.h>
#include <pthread.h>
#include <stdio.h>

static int live_windows, live_views;
static bool fail_window_init, fail_view_init, fail_record_alloc;

@interface OwnershipWindow : NSWindow
@end
@implementation OwnershipWindow
+ (id)allocWithZone:(NSZone *)zone {
    id object = [super allocWithZone:zone];
    if (object) live_windows++;
    return object;
}
- (id)initWithContentRect:(NSRect)rect styleMask:(NSWindowStyleMask)style
                 backing:(NSBackingStoreType)backing defer:(BOOL)defer {
    if (fail_window_init) { [self release]; return nil; }
    return [super initWithContentRect:rect styleMask:style backing:backing defer:defer];
}
- (void)dealloc { live_windows--; [super dealloc]; }
@end

@interface OwnershipView : NSImageView
@end
@implementation OwnershipView
+ (id)allocWithZone:(NSZone *)zone {
    id object = [super allocWithZone:zone];
    if (object) live_views++;
    return object;
}
- (id)initWithFrame:(NSRect)frame {
    if (fail_view_init) { [self release]; return nil; }
    return [super initWithFrame:frame];
}
- (void)dealloc { live_views--; [super dealloc]; }
@end

static void *ownership_calloc(size_t count, size_t size) {
    return fail_record_alloc ? NULL : calloc(count, size);
}
#define NSWindow OwnershipWindow
#define NSImageView OwnershipView
#define calloc ownership_calloc
#include "../../../src/runtime/hosted_cocoa.c"
#undef calloc
#undef NSImageView
#undef NSWindow

const char *rt_string_data(int64_t value) { (void)value; return NULL; }
int64_t rt_string_len(int64_t value) { (void)value; return 0; }

static void expect_empty(void) {
    /* AppKit releases display/animation references on later run-loop turns.
     * Drain actual application events; bound the wait so a leak fails. */
    for (int tick = 0; tick < 100 && (live_windows || live_views); tick++) {
        @autoreleasepool {
            NSEvent *event;
            while ((event = [NSApp nextEventMatchingMask:NSEventMaskAny
                                              untilDate:[NSDate distantPast]
                                                 inMode:NSDefaultRunLoopMode dequeue:YES])) {
                [NSApp sendEvent:event];
            }
            [NSApp updateWindows];
            [[NSRunLoop currentRunLoop] runUntilDate:[NSDate dateWithTimeIntervalSinceNow:0.01]];
        }
    }
    if (live_windows || live_views) {
        fprintf(stderr, "live windows=%d views=%d; expected 0 0\n", live_windows, live_views);
        abort();
    }
    for (int i = 0; i < MAX_HANDLES; i++) assert(g_handles[i].id == 0);
}

static void *close_off_main(void *arg) {
    int64_t id = *(int64_t *)arg;
    assert(!rt_cocoa_window_close(id));
    return NULL;
}

int main(int argc, char **argv) {
    const char *mode = argc > 1 ? argv[1] : "normal";
    bool record = !strcmp(mode, "record-failure");
    bool full = !strcmp(mode, "table-full");
    bool window = !strcmp(mode, "window-failure");
    bool view = !strcmp(mode, "view-failure");
    bool user_close = !strcmp(mode, "user-close");
    bool thread = !strcmp(mode, "thread");
    assert(record || full || window || view || user_close || thread || !strcmp(mode, "normal"));
    int iterations = (record || full || window || view) ? 1 : 20;
    for (int n = 0; n < iterations; n++) {
        @autoreleasepool {
            fail_record_alloc = record;
            fail_window_init = window;
            fail_view_init = view;
            if (full) {
                for (int i = 0; i < MAX_HANDLES; i++) {
                    g_handles[i] = (HandleEntry){i + 1, NULL, KIND_LAYER};
                }
            }
            int64_t id = rt_cocoa_window_new(64, 64, 0);
            if (record || full || window || view) {
                assert(id == COCOA_INVALID_HANDLE);
                if (full) memset(g_handles, 0, sizeof(g_handles));
            } else {
                assert(id != COCOA_INVALID_HANDLE);
                CocoaWindow *wnd = handle_get(id, KIND_WINDOW);
                assert(wnd && wnd->ns_window && wnd->ns_view);
                if (thread) {
                    pthread_t worker;
                    assert(pthread_create(&worker, NULL, close_off_main, &id) == 0);
                    assert(pthread_join(worker, NULL) == 0);
                    assert(handle_get(id, KIND_WINDOW) == wnd);
                }
                if (user_close) {
                    @autoreleasepool { [wnd->ns_window performClose:nil]; }
                    assert(![wnd->ns_window isVisible]);
                }
                assert(rt_cocoa_window_resize(id, 32, 32));
                int64_t layer = rt_cocoa_layer_create(id, 32, 32, 0xff123456);
                assert(layer != COCOA_INVALID_HANDLE);
                assert(rt_cocoa_layer_present(id, layer));
                assert(rt_cocoa_layer_free(layer));
                assert(rt_cocoa_window_close(id));
                assert(!rt_cocoa_window_close(id));
            }
        }
        expect_empty();
    }
    printf("Cocoa window ownership: PASS (%s, %d cycles)\n", mode, iterations);
    return 0;
}
