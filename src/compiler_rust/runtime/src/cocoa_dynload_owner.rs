//! Public Cocoa ABI owned by libsimple_runtime.dylib on macOS.
//!
//! The Objective-C implementation is compiled under private names. Keeping
//! these no_mangle definitions in this crate makes rustc include them in its
//! cdylib export list instead of hiding C object symbols during linking.

macro_rules! cocoa_forward {
    ($public:ident, $implementation:ident, ($($arg:ident: $ty:ty),*) -> $result:ty) => {
        unsafe extern "C" {
            fn $implementation($($arg: $ty),*) -> $result;
        }

        #[no_mangle]
        pub unsafe extern "C" fn $public($($arg: $ty),*) -> $result {
            unsafe { $implementation($($arg),*) }
        }
    };
}

cocoa_forward!(rt_cocoa_window_new, simple_cocoa_impl_window_new,
    (w: i64, h: i64, title_rv: i64) -> i64);
cocoa_forward!(rt_cocoa_window_resize, simple_cocoa_impl_window_resize,
    (win: i64, w: i64, h: i64) -> bool);
cocoa_forward!(rt_cocoa_window_close, simple_cocoa_impl_window_close,
    (win: i64) -> bool);
cocoa_forward!(rt_cocoa_layer_create, simple_cocoa_impl_layer_create,
    (win: i64, w: i64, h: i64, fill_color: i64) -> i64);
cocoa_forward!(rt_cocoa_layer_fill_rect, simple_cocoa_impl_layer_fill_rect,
    (layer: i64, x: i64, y: i64, w: i64, h: i64, color: i64) -> bool);
cocoa_forward!(rt_cocoa_layer_present, simple_cocoa_impl_layer_present,
    (win: i64, layer: i64) -> bool);
cocoa_forward!(rt_cocoa_layer_free, simple_cocoa_impl_layer_free,
    (layer: i64) -> bool);
cocoa_forward!(rt_cocoa_layer_read_pixel, simple_cocoa_impl_layer_read_pixel,
    (layer: i64, x: i64, y: i64) -> i64);
cocoa_forward!(rt_cocoa_layer_blend_rect, simple_cocoa_impl_layer_blend_rect,
    (layer: i64, x: i64, y: i64, w: i64, h: i64, color: i64, alpha: i64) -> bool);
cocoa_forward!(rt_cocoa_layer_blur, simple_cocoa_impl_layer_blur,
    (layer: i64, x: i64, y: i64, w: i64, h: i64, radius: i64) -> bool);
cocoa_forward!(rt_cocoa_layer_gradient_v, simple_cocoa_impl_layer_gradient_v,
    (layer: i64, x: i64, y: i64, w: i64, h: i64, color_top: i64, color_bottom: i64) -> bool);
cocoa_forward!(rt_cocoa_event_pump, simple_cocoa_impl_event_pump,
    (win: i64) -> i64);
