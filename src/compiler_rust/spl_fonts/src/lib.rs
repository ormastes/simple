// spl_fonts — Phase 1 font rasterization FFI backed by fontdue.
//
// C ABI entry points, all i64-in / i64-out, using a single global slot
// for the loaded font and a single global slot for the most recently
// rasterized glyph bitmap. This is deliberately minimal — Phase 2 will grow a
// proper handle table.

use std::ffi::CString;
use std::os::raw::{c_char, c_int, c_long, c_uint, c_void};
use std::sync::Mutex;

use fontdue::layout::{CoordinateSystem, Layout, LayoutSettings, TextStyle};
use fontdue::{Font, FontSettings, Metrics, OutlineBounds};

struct GlyphSlot {
    metrics: Metrics,
    bitmap: Vec<u8>,
    width: usize,
    height: usize,
    advance_width: f32,
    xmin: i32,
    ymin: i32,
}

struct LayoutGlyphSlot {
    codepoint: i64,
    x: i64,
    y: i64,
    width: i64,
    height: i64,
    byte_offset: i64,
}

static FONT_SLOT: Mutex<Option<Font>> = Mutex::new(None);
static FREETYPE_SLOT: Mutex<Option<FreetypeSlot>> = Mutex::new(None);
static GLYPH_SLOT: Mutex<Option<GlyphSlot>> = Mutex::new(None);
static LAYOUT_SLOT: Mutex<Vec<LayoutGlyphSlot>> = Mutex::new(Vec::new());

struct FreetypeSlot {
    library: usize,
    face: usize,
}

#[repr(C)]
#[derive(Copy, Clone)]
struct FtVector {
    x: c_long,
    y: c_long,
}

#[repr(C)]
#[derive(Copy, Clone)]
struct FtGeneric {
    data: *mut c_void,
    finalizer: Option<unsafe extern "C" fn(*mut c_void)>,
}

#[repr(C)]
#[derive(Copy, Clone)]
struct FtBBox {
    x_min: c_long,
    y_min: c_long,
    x_max: c_long,
    y_max: c_long,
}

#[repr(C)]
#[derive(Copy, Clone)]
struct FtBitmap {
    rows: c_uint,
    width: c_uint,
    pitch: c_int,
    buffer: *mut u8,
    num_grays: u16,
    pixel_mode: u8,
    palette_mode: u8,
    palette: *mut c_void,
}

#[repr(C)]
#[derive(Copy, Clone)]
struct FtGlyphMetrics {
    width: c_long,
    height: c_long,
    hori_bearing_x: c_long,
    hori_bearing_y: c_long,
    hori_advance: c_long,
    vert_bearing_x: c_long,
    vert_bearing_y: c_long,
    vert_advance: c_long,
}

#[repr(C)]
struct FtGlyphSlotRec {
    library: *mut c_void,
    face: *mut c_void,
    next: *mut c_void,
    glyph_index: c_uint,
    generic: FtGeneric,
    metrics: FtGlyphMetrics,
    linear_hori_advance: c_long,
    linear_vert_advance: c_long,
    advance: FtVector,
    format: c_uint,
    bitmap: FtBitmap,
    bitmap_left: c_int,
    bitmap_top: c_int,
}

#[repr(C)]
struct FtFaceRec {
    num_faces: c_long,
    face_index: c_long,
    face_flags: c_long,
    style_flags: c_long,
    num_glyphs: c_long,
    family_name: *mut c_char,
    style_name: *mut c_char,
    num_fixed_sizes: c_int,
    available_sizes: *mut c_void,
    num_charmaps: c_int,
    charmaps: *mut c_void,
    generic: FtGeneric,
    bbox: FtBBox,
    units_per_em: u16,
    ascender: i16,
    descender: i16,
    height: i16,
    max_advance_width: i16,
    max_advance_height: i16,
    underline_position: i16,
    underline_thickness: i16,
    glyph: *mut FtGlyphSlotRec,
}

#[link(name = "freetype")]
extern "C" {
    fn FT_Init_FreeType(alibrary: *mut *mut c_void) -> c_int;
    fn FT_New_Face(library: *mut c_void, filepathname: *const c_char, face_index: c_long, aface: *mut *mut FtFaceRec) -> c_int;
    fn FT_Done_Face(face: *mut FtFaceRec) -> c_int;
    fn FT_Done_FreeType(library: *mut c_void) -> c_int;
    fn FT_Set_Pixel_Sizes(face: *mut FtFaceRec, pixel_width: c_uint, pixel_height: c_uint) -> c_int;
    fn FT_Load_Char(face: *mut FtFaceRec, char_code: c_ulong, load_flags: c_int) -> c_int;
}

type c_ulong = std::os::raw::c_ulong;

const FT_LOAD_RENDER: c_int = 0x4;
const FT_LOAD_TARGET_NORMAL: c_int = 0x0;

/// Load a TTF/OTF from `path_ptr`/`path_len`. Returns 1 on success, 0 on any failure.
#[no_mangle]
pub extern "C" fn rt_fonts_init(path_ptr: i64, path_len: i64) -> i64 {
    if path_ptr == 0 || path_len <= 0 {
        return 0;
    }
    let slice = unsafe { std::slice::from_raw_parts(path_ptr as *const u8, path_len as usize) };
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
    let freetype = load_freetype_face(path);
    match FONT_SLOT.lock() {
        Ok(mut slot) => {
            *slot = Some(font);
            if let Ok(mut ft_slot) = FREETYPE_SLOT.lock() {
                if let Some(old) = ft_slot.take() {
                    unsafe {
                        let _ = FT_Done_Face(old.face as *mut FtFaceRec);
                        let _ = FT_Done_FreeType(old.library as *mut c_void);
                    }
                }
                *ft_slot = freetype;
            }
            1
        }
        Err(_) => 0,
    }
}

fn load_freetype_face(path: &str) -> Option<FreetypeSlot> {
    let c_path = CString::new(path).ok()?;
    unsafe {
        let mut library: *mut c_void = std::ptr::null_mut();
        if FT_Init_FreeType(&mut library) != 0 || library.is_null() {
            return None;
        }
        let mut face: *mut FtFaceRec = std::ptr::null_mut();
        if FT_New_Face(library, c_path.as_ptr(), 0, &mut face) != 0 || face.is_null() {
            let _ = FT_Done_FreeType(library);
            return None;
        }
        Some(FreetypeSlot {
            library: library as usize,
            face: face as usize,
        })
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
    let glyph = match rasterize_with_freetype(ch, font_size_px) {
        Some(glyph) => glyph,
        None => {
            let (metrics, bitmap) = font.rasterize(ch, font_size_px as f32);
            GlyphSlot {
                width: metrics.width,
                height: metrics.height,
                advance_width: metrics.advance_width,
                xmin: metrics.xmin,
                ymin: metrics.ymin,
                metrics,
                bitmap,
            }
        }
    };
    match GLYPH_SLOT.lock() {
        Ok(mut slot) => {
            *slot = Some(glyph);
            1
        }
        Err(_) => 0,
    }
}

fn rasterize_with_freetype(ch: char, font_size_px: i64) -> Option<GlyphSlot> {
    let ft_guard = FREETYPE_SLOT.lock().ok()?;
    let ft = ft_guard.as_ref()?;
    unsafe {
        let face = ft.face as *mut FtFaceRec;
        if face.is_null() {
            return None;
        }
        if FT_Set_Pixel_Sizes(face, 0, font_size_px as c_uint) != 0 {
            return None;
        }
        if FT_Load_Char(face, ch as c_ulong, FT_LOAD_RENDER | FT_LOAD_TARGET_NORMAL) != 0 {
            return None;
        }
        let slot = (*face).glyph;
        if slot.is_null() {
            return None;
        }
        let bitmap_ref = &(*slot).bitmap;
        let width = bitmap_ref.width as usize;
        let height = bitmap_ref.rows as usize;
        let pitch = bitmap_ref.pitch.unsigned_abs() as usize;
        let mut bitmap = Vec::with_capacity(width * height);
        if width > 0 && height > 0 {
            if bitmap_ref.buffer.is_null() {
                return None;
            }
            for y in 0..height {
                let row = std::slice::from_raw_parts(bitmap_ref.buffer.add(y * pitch), pitch);
                for x in 0..width {
                    bitmap.push(*row.get(x).unwrap_or(&0));
                }
            }
        }
        let advance_width = ((*slot).advance.x as f32 / 64.0).round();
        let ymin = (*slot).bitmap_top - bitmap_ref.rows as c_int;
        let metrics = Metrics {
            xmin: (*slot).bitmap_left,
            ymin,
            width,
            height,
            advance_width,
            advance_height: ((*slot).advance.y as f32 / 64.0).round(),
            bounds: OutlineBounds {
                xmin: (*slot).bitmap_left as f32,
                ymin: ymin as f32,
                width: width as f32,
                height: height as f32,
            },
        };
        Some(GlyphSlot {
            metrics,
            bitmap,
            width,
            height,
            advance_width,
            xmin: (*slot).bitmap_left,
            ymin,
        })
    }
}

/// Rasterize a single codepoint using fontdue's RGB subpixel coverage.
///
/// The metric width/height remain in whole pixels; the bitmap stores three
/// coverage samples per pixel in row-major RGB order.
#[no_mangle]
pub extern "C" fn rt_fonts_rasterize_glyph_subpixel(codepoint: i64, font_size_px: i64) -> i64 {
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
    let (metrics, bitmap) = font.rasterize_subpixel(ch, font_size_px as f32);
    match GLYPH_SLOT.lock() {
        Ok(mut slot) => {
            *slot = Some(GlyphSlot {
                width: metrics.width,
                height: metrics.height,
                advance_width: metrics.advance_width,
                xmin: metrics.xmin,
                ymin: metrics.ymin,
                metrics,
                bitmap,
            });
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
///   4 = bitmap ymin/bottom offset (px, rounded)
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

/// Return rounded horizontal kerning in pixels for a left/right codepoint pair.
#[no_mangle]
pub extern "C" fn rt_fonts_horizontal_kern(left_codepoint: i64, right_codepoint: i64, font_size_px: i64) -> i64 {
    if font_size_px <= 0 {
        return 0;
    }
    let left = match char::from_u32(left_codepoint as u32) {
        Some(c) => c,
        None => return 0,
    };
    let right = match char::from_u32(right_codepoint as u32) {
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
    font.horizontal_kern(left, right, font_size_px as f32)
        .map(|v| v.round() as i64)
        .unwrap_or(0)
}

/// Return rounded horizontal line metrics for the active font.
///
/// Fields:
///   0 = ascent
///   1 = descent
///   2 = line gap
///   3 = new line size
#[no_mangle]
pub extern "C" fn rt_fonts_horizontal_line_metric(font_size_px: i64, field: i64) -> i64 {
    if font_size_px <= 0 {
        return 0;
    }
    let font_guard = match FONT_SLOT.lock() {
        Ok(g) => g,
        Err(_) => return 0,
    };
    let font = match font_guard.as_ref() {
        Some(f) => f,
        None => return 0,
    };
    let metrics = match font.horizontal_line_metrics(font_size_px as f32) {
        Some(m) => m,
        None => return 0,
    };
    match field {
        0 => metrics.ascent.round() as i64,
        1 => metrics.descent.round() as i64,
        2 => metrics.line_gap.round() as i64,
        3 => metrics.new_line_size.round() as i64,
        _ => 0,
    }
}

/// Layout UTF-8 text with fontdue's layout engine and store positioned glyphs
/// in a global readback slot. Returns the glyph count, or -1 on invalid input.
#[no_mangle]
pub extern "C" fn rt_fonts_layout_text(text_ptr: i64, text_len: i64, font_size_px: i64, max_width_px: i64) -> i64 {
    if text_ptr == 0 || text_len < 0 || font_size_px <= 0 {
        return -1;
    }
    let slice = unsafe { std::slice::from_raw_parts(text_ptr as *const u8, text_len as usize) };
    let text = match std::str::from_utf8(slice) {
        Ok(s) => s,
        Err(_) => return -1,
    };
    let font_guard = match FONT_SLOT.lock() {
        Ok(g) => g,
        Err(_) => return -1,
    };
    let font = match font_guard.as_ref() {
        Some(f) => f,
        None => return -1,
    };
    let mut settings = LayoutSettings::default();
    settings.x = 0.0;
    settings.y = 0.0;
    if max_width_px > 0 {
        settings.max_width = Some(max_width_px as f32);
    }
    let mut layout = Layout::new(CoordinateSystem::PositiveYDown);
    layout.reset(&settings);
    layout.append(&[font], &TextStyle::new(text, font_size_px as f32, 0));

    let mut out = Vec::new();
    for glyph in layout.glyphs() {
        out.push(LayoutGlyphSlot {
            codepoint: glyph.parent as i64,
            x: glyph.x.round() as i64,
            y: glyph.y.round() as i64,
            width: glyph.width as i64,
            height: glyph.height as i64,
            byte_offset: glyph.byte_offset as i64,
        });
    }
    let count = out.len() as i64;
    match LAYOUT_SLOT.lock() {
        Ok(mut slot) => {
            *slot = out;
            count
        }
        Err(_) => -1,
    }
}

/// Return a field for a glyph from the most recent layout slot.
///
/// Fields:
///   0 = Unicode codepoint
///   1 = x
///   2 = y
///   3 = width
///   4 = height
///   5 = byte offset
#[no_mangle]
pub extern "C" fn rt_fonts_layout_glyph_metric(index: i64, field: i64) -> i64 {
    if index < 0 {
        return 0;
    }
    let guard = match LAYOUT_SLOT.lock() {
        Ok(g) => g,
        Err(_) => return 0,
    };
    let glyph = match guard.get(index as usize) {
        Some(g) => g,
        None => return 0,
    };
    match field {
        0 => glyph.codepoint,
        1 => glyph.x,
        2 => glyph.y,
        3 => glyph.width,
        4 => glyph.height,
        5 => glyph.byte_offset,
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

/// Return RGB subpixel coverage (0..=255) for pixel (x,y), channel 0..2.
#[no_mangle]
pub extern "C" fn rt_fonts_glyph_subpixel_pixel(handle: i64, x: i64, y: i64, channel: i64) -> i64 {
    if handle != 1 || x < 0 || y < 0 || channel < 0 || channel > 2 {
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
    let idx = yu * w * 3 + xu * 3 + channel as usize;
    glyph.bitmap.get(idx).copied().map(|b| b as i64).unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use super::*;

    const LIBERATION_SERIF: &str = "/usr/share/fonts/truetype/liberation/LiberationSerif-Regular.ttf";

    fn init_liberation_serif() -> bool {
        if !std::path::Path::new(LIBERATION_SERIF).exists() {
            return false;
        }
        rt_fonts_init(LIBERATION_SERIF.as_ptr() as i64, LIBERATION_SERIF.len() as i64) == 1
    }

    #[test]
    fn horizontal_kern_rejects_invalid_inputs() {
        assert_eq!(rt_fonts_horizontal_kern('A' as i64, 'V' as i64, 0), 0);
        assert_eq!(rt_fonts_horizontal_kern(-1, 'V' as i64, 16), 0);
    }

    #[test]
    fn horizontal_kern_returns_font_pair_adjustment_when_available() {
        if !init_liberation_serif() {
            return;
        }
        let av = rt_fonts_horizontal_kern('A' as i64, 'V' as i64, 16);
        assert!(av <= 0, "expected AV kerning to be non-positive, got {av}");
    }

    #[test]
    fn horizontal_line_metrics_return_scaled_values() {
        if !init_liberation_serif() {
            return;
        }
        let ascent = rt_fonts_horizontal_line_metric(16, 0);
        let descent = rt_fonts_horizontal_line_metric(16, 1);
        let new_line_size = rt_fonts_horizontal_line_metric(16, 3);
        assert!(ascent > 0, "expected positive ascent, got {ascent}");
        assert!(descent < 0, "expected negative descent, got {descent}");
        assert!(new_line_size > 0, "expected positive line size, got {new_line_size}");
        assert_eq!(rt_fonts_horizontal_line_metric(0, 0), 0);
        assert_eq!(rt_fonts_horizontal_line_metric(16, 99), 0);
    }

    #[test]
    fn layout_text_returns_positioned_glyphs() {
        if !init_liberation_serif() {
            return;
        }
        let text = "Google search deterministic compatibility fixture";
        let count = rt_fonts_layout_text(text.as_ptr() as i64, text.len() as i64, 16, 112);
        assert!(count > 0, "expected positioned glyphs, got {count}");
        assert_eq!(rt_fonts_layout_glyph_metric(0, 0), 'G' as i64);
        assert_eq!(rt_fonts_layout_glyph_metric(0, 1), 0);
        assert!(rt_fonts_layout_glyph_metric(0, 4) > 0);
        assert_eq!(rt_fonts_layout_text(0, text.len() as i64, 16, 112), -1);
    }

    #[test]
    fn subpixel_rasterize_returns_rgb_triplet_coverage() {
        if !init_liberation_serif() {
            return;
        }
        let handle = rt_fonts_rasterize_glyph_subpixel('G' as i64, 16);
        assert_eq!(handle, 1);
        let width = rt_fonts_glyph_metric(handle, 0);
        let height = rt_fonts_glyph_metric(handle, 1);
        assert!(width > 0, "expected positive width, got {width}");
        assert!(height > 0, "expected positive height, got {height}");
        let mut max_sample = 0;
        for y in 0..height {
            for x in 0..width {
                for channel in 0..3 {
                    max_sample = max_sample.max(rt_fonts_glyph_subpixel_pixel(handle, x, y, channel));
                }
            }
        }
        assert!(max_sample > 0, "expected non-empty subpixel coverage");
        assert_eq!(rt_fonts_glyph_subpixel_pixel(handle, 0, 0, 99), 0);
    }

    #[test]
    fn glyph_metric_field_four_is_bitmap_ymin_not_layout_top() {
        if !init_liberation_serif() {
            return;
        }
        let handle = rt_fonts_rasterize_glyph('G' as i64, 16);
        assert_eq!(handle, 1);
        let metric_ymin = rt_fonts_glyph_metric(handle, 4);
        let font = FONT_SLOT.lock().unwrap();
        let font = font.as_ref().unwrap();
        let (metrics, _) = font.rasterize('G', 16.0);
        assert_eq!(metric_ymin, metrics.ymin as i64);
    }
}
