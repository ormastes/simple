/* macOS MRC ownership regression. No visible window or application required.
 * clang -fno-objc-arc -framework Cocoa \
 *   test/01_unit/runtime/hosted_cocoa_frame_ownership_test.m -o /tmp/cocoa-ownership
 * /tmp/cocoa-ownership
 */
#import <Cocoa/Cocoa.h>
#include <assert.h>
#include <stdio.h>

static int live_bitmaps, live_images;
static bool fail_bitmap_alloc, fail_bitmap_data, fail_image_init;

@interface OwnershipBitmap : NSBitmapImageRep
@end
@implementation OwnershipBitmap
+ (id)allocWithZone:(NSZone *)zone {
    if (fail_bitmap_alloc) return nil;
    id object = [super allocWithZone:zone];
    if (object) live_bitmaps++;
    return object;
}
- (unsigned char *)bitmapData {
    return fail_bitmap_data ? NULL : [super bitmapData];
}
- (void)dealloc {
    live_bitmaps--;
    [super dealloc];
}
@end

@interface OwnershipImage : NSImage
@end
@implementation OwnershipImage
+ (id)allocWithZone:(NSZone *)zone {
    id object = [super allocWithZone:zone];
    if (object) live_images++;
    return object;
}
- (id)initWithSize:(NSSize)size {
    if (fail_image_init) {
        [self release];
        return nil;
    }
    return [super initWithSize:size];
}
- (void)dealloc {
    live_images--;
    [super dealloc];
}
@end

/* Exercise the production function and AppKit's real retaining setters. Only
 * allocation classes are substituted, to count their actual deallocation. */
#define NSBitmapImageRep OwnershipBitmap
#define NSImage OwnershipImage
#include "../../../src/runtime/hosted_cocoa.c"
#undef NSImage
#undef NSBitmapImageRep

const char *rt_string_data(int64_t value) { (void)value; return NULL; }
int64_t rt_string_len(int64_t value) { (void)value; return 0; }

static void expect_live(int bitmaps, int images) {
    if (live_bitmaps != bitmaps || live_images != images) {
        fprintf(stderr, "live objects: bitmap=%d image=%d; expected %d %d\n",
                live_bitmaps, live_images, bitmaps, images);
        abort();
    }
}

int main(void) {
    @autoreleasepool {
        CocoaWindow window = {0};
        window.ns_view = [[NSImageView alloc] initWithFrame:NSMakeRect(0, 0, 64, 64)];
        assert(window.ns_view);
        int64_t window_id = next_handle();
        assert(handle_insert(window_id, &window, KIND_WINDOW));
        int64_t layer_id = rt_cocoa_layer_create(window_id, 64, 64, 0xff123456);
        assert(layer_id != COCOA_INVALID_HANDLE);

        /* Each replaced frame must die when the production autorelease pool
         * drains. Only the current image and its representation remain live. */
        for (int frame = 0; frame < 100; frame++) {
            @autoreleasepool {
                assert(rt_cocoa_layer_present(window_id, layer_id));
                NSBitmapImageRep *bitmap = (NSBitmapImageRep *)[[[window.ns_view image] representations] objectAtIndex:0];
                unsigned char *rgba = [bitmap bitmapData];
                assert(rgba[0] == 0x12 && rgba[1] == 0x34 && rgba[2] == 0x56 && rgba[3] == 0xff);
            }
            expect_live(1, 1);
        }

        fail_bitmap_alloc = true;
        assert(!rt_cocoa_layer_present(window_id, layer_id));
        fail_bitmap_alloc = false;
        expect_live(1, 1);

        fail_bitmap_data = true;
        assert(!rt_cocoa_layer_present(window_id, layer_id));
        fail_bitmap_data = false;
        expect_live(1, 1);

        fail_image_init = true;
        assert(!rt_cocoa_layer_present(window_id, layer_id));
        fail_image_init = false;
        expect_live(1, 1);

        assert(rt_cocoa_layer_present(window_id, layer_id));
        expect_live(1, 1);
        @autoreleasepool { [window.ns_view setImage:nil]; }
        expect_live(0, 0);
        [window.ns_view release];
        assert(handle_remove(window_id, KIND_WINDOW) == &window);
        assert(rt_cocoa_layer_free(layer_id));
    }
    puts("Cocoa frame ownership: PASS (100 replacements, three failure paths, teardown)");
    return 0;
}
