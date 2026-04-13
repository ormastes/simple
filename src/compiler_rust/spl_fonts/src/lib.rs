// spl_fonts — Phase 1 font rasterization FFI backed by fontdue.
//
// Four C ABI entry points, all i64-in / i64-out, using a single global slot
// for the loaded font and a single global slot for the most recently
// rasterized glyph bitmap. This is deliberately minimal — Phase 2 will grow a
// proper handle table.

use std::sync::Mutex;

use fontdue::{Font, FontSettings, Metrics};

struct GlyphSlot {
    metrics: Metrics,
    bitmap: Vec<u8>,
}

static FONT_SLOT: Mutex<Option<Font>> = Mutex::new(None);
static GLYPH_SLOT: Mutex<Option<GlyphSlot>> = Mutex::new(None);

/// Load a TTF/OTF from `path_ptr`/`path_len`. Returns 1 on success, 0 on any failure.
#[no_mangle]
pub extern "C" fn rt_fonts_init(path_ptr: i64, path_len: i64) -> i64 {
    if path_ptr == 0 || path_len <= 0 {
        return 0;
    }
    let slice = unsafe {
        std::slice::from_raw_parts(path_ptr as *const u8, path_len as usize)
    };
    let path = match std::str::from_utf8(slice) {
        Ok(s) => s,
        Err(_) => return 0,
    };
    let bytes = match std::fs::read(path) {
        Ok(b) => b,
        Err(_) => return 0,
    };
    let font = match Font::from_bytes(bytes, FontSettings::default()) {
        Ok(f) => f,
        Err(_) => return 0,
    };
    match FONT_SLOT.lock() {
        Ok(mut slot) => {
            *slot = Some(font);
            1
        }
        Err(_) => 0,
    }
}

/// Rasterize a single codepoint at a pixel size. Returns an opaque handle
/// (1 for the one-and-only global slot, 0 on failure).
#[no_mangle]
pub extern "C" fn rt_fonts_rasterize_glyph(codepoint: i64, font_size_px: i64) -> i64 {
    if font_size_px <= 0 {
        return 0;
    }
    let ch = match char::from_u32(codepoint as u32) {
        Some(c) => c,
        None => return 0,
    };
    let font_guard = match FONT_SLOT.lock() {
        Ok(g) => g,
        Err(_) => return 0,
    };
    let font = match font_guard.as_ref() {
        Some(f) => f,
        None => return 0,
    };
    let (metrics, bitmap) = font.rasterize(ch, font_size_px as f32);
    match GLYPH_SLOT.lock() {
        Ok(mut slot) => {
            *slot = Some(GlyphSlot { metrics, bitmap });
            1
        }
        Err(_) => 0,
    }
}

/// Return a metric field for the most recent glyph. Fields:
///   0 = width (px)
///   1 = height (px)
///   2 = advance (px, rounded)
///   3 = bearing_x (px, rounded)
///   4 = bearing_y (px, rounded)
#[no_mangle]
pub extern "C" fn rt_fonts_glyph_metric(handle: i64, field: i64) -> i64 {
    if handle != 1 {
        return 0;
    }
    let guard = match GLYPH_SLOT.lock() {
        Ok(g) => g,
        Err(_) => return 0,
    };
    let glyph = match guard.as_ref() {
        Some(g) => g,
        None => return 0,
    };
    match field {
        0 => glyph.metrics.width as i64,
        1 => glyph.metrics.height as i64,
        2 => glyph.metrics.advance_width.round() as i64,
        3 => glyph.metrics.xmin as i64,
        4 => glyph.metrics.ymin as i64,
        _ => 0,
    }
}

/// Return the alpha coverage (0..=255) for pixel (x,y) in the most recent
/// glyph bitmap. Out-of-bounds reads return 0.
#[no_mangle]
pub extern "C" fn rt_fonts_glyph_pixel(handle: i64, x: i64, y: i64) -> i64 {
    if handle != 1 || x < 0 || y < 0 {
        return 0;
    }
    let guard = match GLYPH_SLOT.lock() {
        Ok(g) => g,
        Err(_) => return 0,
    };
    let glyph = match guard.as_ref() {
        Some(g) => g,
        None => return 0,
    };
    let w = glyph.metrics.width;
    let h = glyph.metrics.height;
    let (xu, yu) = (x as usize, y as usize);
    if xu >= w || yu >= h {
        return 0;
    }
    let idx = yu * w + xu;
    glyph.bitmap.get(idx).copied().map(|b| b as i64).unwrap_or(0)
}
