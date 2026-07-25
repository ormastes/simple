// spl_fonts — Phase 1 font rasterization SFFI backed by fontdue.
//
// C ABI entry points, all i64-in / i64-out. The loaded face is process-global;
// each rasterized glyph is an owned snapshot released by rt_fonts_glyph_free.

use std::ffi::CString;
use std::os::raw::{c_char, c_int, c_long, c_uint, c_void};
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::Mutex;

use fontdue::layout::{CoordinateSystem, Layout, LayoutSettings, TextStyle};
use fontdue::{Font, FontSettings, Metrics, OutlineBounds};
use sha2::{Digest, Sha256};

struct GlyphSlot {
    metrics: Metrics,
    bitmap: Vec<u8>,
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
static LAYOUT_SLOT: Mutex<Vec<LayoutGlyphSlot>> = Mutex::new(Vec::new());
static FONT_GENERATION: AtomicI64 = AtomicI64::new(0);
// ponytail: process-global face/layout; add owned face/layout handles only when
// concurrent distinct-font rendering becomes a selected requirement.

struct FreetypeSlot {
    library: usize,
    face: usize,
    _bytes: Vec<u8>,
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
    fn FT_New_Face(
        library: *mut c_void,
        filepathname: *const c_char,
        face_index: c_long,
        aface: *mut *mut FtFaceRec,
    ) -> c_int;
    fn FT_New_Memory_Face(
        library: *mut c_void,
        file_base: *const u8,
        file_size: c_long,
        face_index: c_long,
        aface: *mut *mut FtFaceRec,
    ) -> c_int;
    fn FT_Done_Face(face: *mut FtFaceRec) -> c_int;
    fn FT_Done_FreeType(library: *mut c_void) -> c_int;
    fn FT_Set_Pixel_Sizes(face: *mut FtFaceRec, pixel_width: c_uint, pixel_height: c_uint) -> c_int;
    fn FT_Load_Char(face: *mut FtFaceRec, char_code: CUlong, load_flags: c_int) -> c_int;
    fn FT_Library_SetLcdFilter(library: *mut c_void, filter: c_uint) -> c_int;
}

type CUlong = std::os::raw::c_ulong;

const FT_LOAD_RENDER: c_int = 0x4;
const FT_LOAD_TARGET_NORMAL: c_int = 0x0;
const FT_LOAD_TARGET_LCD: c_int = 3 << 16;
const FT_LCD_FILTER_DEFAULT: c_uint = 1;
const MAX_VERIFIED_FONT_BYTES: i64 = 256 * 1024 * 1024;

fn lowercase_sha256_hex(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn exact_lowercase_sha256(value: &[u8]) -> bool {
    value.len() == 64
        && value
            .iter()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(byte))
}

fn constant_time_equal(left: &[u8], right: &[u8]) -> bool {
    if left.len() != right.len() {
        return false;
    }
    let mut difference = 0u8;
    for (a, b) in left.iter().zip(right) {
        difference |= a ^ b;
    }
    difference == 0
}

fn destroy_freetype_slot(slot: FreetypeSlot) {
    unsafe {
        let _ = FT_Done_Face(slot.face as *mut FtFaceRec);
        let _ = FT_Done_FreeType(slot.library as *mut c_void);
    }
}

/// Load verified caller-owned font bytes. Returns 1 only after both rasterizers
/// are ready; every failure preserves the prior face and generation.
#[no_mangle]
pub extern "C" fn rt_fonts_init_verified_bytes(
    data_ptr: i64,
    data_len: i64,
    expected_sha256_ptr: i64,
    expected_sha256_len: i64,
) -> i64 {
    if data_ptr == 0
        || data_len <= 0
        || data_len > MAX_VERIFIED_FONT_BYTES
        || expected_sha256_ptr == 0
        || expected_sha256_len != 64
    {
        return 0;
    }
    let expected =
        unsafe { std::slice::from_raw_parts(expected_sha256_ptr as *const u8, expected_sha256_len as usize) };
    if !exact_lowercase_sha256(expected) {
        return 0;
    }
    let caller = unsafe { std::slice::from_raw_parts(data_ptr as *const u8, data_len as usize) };
    let font_bytes = caller.to_vec();
    let actual = lowercase_sha256_hex(&font_bytes);
    if !constant_time_equal(actual.as_bytes(), expected) {
        return 0;
    }
    let font = match Font::from_bytes(font_bytes.clone(), FontSettings::default()) {
        Ok(font) => font,
        Err(_) => return 0,
    };
    let freetype = match load_freetype_memory_face(font_bytes) {
        Some(slot) => slot,
        None => return 0,
    };

    let mut font_slot = match FONT_SLOT.lock() {
        Ok(slot) => slot,
        Err(_) => {
            destroy_freetype_slot(freetype);
            return 0;
        }
    };
    let mut freetype_slot = match FREETYPE_SLOT.lock() {
        Ok(slot) => slot,
        Err(_) => {
            drop(font_slot);
            destroy_freetype_slot(freetype);
            return 0;
        }
    };
    let old_freetype = freetype_slot.replace(freetype);
    *font_slot = Some(font);
    FONT_GENERATION.fetch_add(1, Ordering::SeqCst);
    drop(freetype_slot);
    drop(font_slot);
    if let Some(old) = old_freetype {
        destroy_freetype_slot(old);
    }
    1
}

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
            FONT_GENERATION.fetch_add(1, Ordering::SeqCst);
            1
        }
        Err(_) => 0,
    }
}

#[no_mangle]
pub extern "C" fn rt_fonts_generation() -> i64 {
    FONT_GENERATION.load(Ordering::SeqCst)
}

#[no_mangle]
pub extern "C" fn rt_fonts_has_glyph(codepoint: i64) -> i64 {
    let ch = match char::from_u32(codepoint as u32) {
        Some(c) => c,
        None => return 0,
    };
    let guard = match FONT_SLOT.lock() {
        Ok(g) => g,
        Err(_) => return 0,
    };
    match guard.as_ref() {
        Some(font) if font.lookup_glyph_index(ch) != 0 => 1,
        _ => 0,
    }
}

fn load_freetype_face(path: &str) -> Option<FreetypeSlot> {
    let c_path = CString::new(path).ok()?;
    unsafe {
        let mut library: *mut c_void = std::ptr::null_mut();
        if FT_Init_FreeType(&mut library) != 0 || library.is_null() {
            return None;
        }
        let _ = FT_Library_SetLcdFilter(library, FT_LCD_FILTER_DEFAULT);
        let mut face: *mut FtFaceRec = std::ptr::null_mut();
        if FT_New_Face(library, c_path.as_ptr(), 0, &mut face) != 0 || face.is_null() {
            let _ = FT_Done_FreeType(library);
            return None;
        }
        Some(FreetypeSlot {
            library: library as usize,
            face: face as usize,
            _bytes: Vec::new(),
        })
    }
}

fn load_freetype_memory_face(bytes: Vec<u8>) -> Option<FreetypeSlot> {
    unsafe {
        let mut library: *mut c_void = std::ptr::null_mut();
        if FT_Init_FreeType(&mut library) != 0 || library.is_null() {
            return None;
        }
        let _ = FT_Library_SetLcdFilter(library, FT_LCD_FILTER_DEFAULT);
        let mut face: *mut FtFaceRec = std::ptr::null_mut();
        if FT_New_Memory_Face(library, bytes.as_ptr(), bytes.len() as c_long, 0, &mut face) != 0 || face.is_null() {
            let _ = FT_Done_FreeType(library);
            return None;
        }
        Some(FreetypeSlot {
            library: library as usize,
            face: face as usize,
            _bytes: bytes,
        })
    }
}

/// Rasterize a single codepoint at a pixel size. Returns an owned opaque
/// snapshot handle, or 0 on failure.
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
            GlyphSlot { metrics, bitmap }
        }
    };
    Box::into_raw(Box::new(glyph)) as i64
}

/// Rasterize only through the loaded native FreeType face. Selected bundled
/// fonts use this entry point so a native miss remains available to the Pure
/// Simple outline fallback instead of being hidden by fontdue.
#[no_mangle]
pub extern "C" fn rt_fonts_rasterize_glyph_native_only(codepoint: i64, font_size_px: i64) -> i64 {
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
    if font.lookup_glyph_index(ch) == 0 {
        return 0;
    }
    match rasterize_with_freetype(ch, font_size_px) {
        Some(glyph) => Box::into_raw(Box::new(glyph)) as i64,
        None => 0,
    }
}

fn glyph_from_handle(handle: i64) -> Option<&'static GlyphSlot> {
    if handle == 0 {
        return None;
    }
    unsafe { (handle as *const GlyphSlot).as_ref() }
}

#[no_mangle]
pub extern "C" fn rt_fonts_glyph_pixels_ptr(handle: i64) -> i64 {
    glyph_from_handle(handle)
        .map(|glyph| glyph.bitmap.as_ptr() as i64)
        .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn rt_fonts_glyph_pixels_len(handle: i64) -> i64 {
    glyph_from_handle(handle)
        .map(|glyph| glyph.bitmap.len() as i64)
        .unwrap_or(0)
}

#[no_mangle]
pub extern "C" fn rt_fonts_glyph_free(handle: i64) -> i64 {
    if handle == 0 {
        return 0;
    }
    unsafe { drop(Box::from_raw(handle as *mut GlyphSlot)) };
    1
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
        if FT_Load_Char(face, ch as CUlong, FT_LOAD_RENDER | FT_LOAD_TARGET_NORMAL) != 0 {
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
        Some(GlyphSlot { metrics, bitmap })
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
    let glyph = match rasterize_subpixel_with_freetype(ch, font_size_px) {
        Some(glyph) => glyph,
        None => {
            let (metrics, bitmap) = font.rasterize_subpixel(ch, font_size_px as f32);
            GlyphSlot { metrics, bitmap }
        }
    };
    Box::into_raw(Box::new(glyph)) as i64
}

fn rasterize_subpixel_with_freetype(ch: char, font_size_px: i64) -> Option<GlyphSlot> {
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
        if FT_Load_Char(face, ch as CUlong, FT_LOAD_RENDER | FT_LOAD_TARGET_LCD) != 0 {
            return None;
        }
        let slot = (*face).glyph;
        if slot.is_null() {
            return None;
        }
        let bitmap_ref = &(*slot).bitmap;
        if bitmap_ref.width == 0 || bitmap_ref.rows == 0 {
            let metrics = Metrics {
                xmin: (*slot).bitmap_left,
                ymin: 0,
                width: 0,
                height: 0,
                advance_width: ((*slot).advance.x as f32 / 64.0).round(),
                advance_height: ((*slot).advance.y as f32 / 64.0).round(),
                bounds: OutlineBounds::default(),
            };
            return Some(GlyphSlot {
                metrics,
                bitmap: Vec::new(),
            });
        }
        if bitmap_ref.buffer.is_null() || !bitmap_ref.width.is_multiple_of(3) {
            return None;
        }
        let visual_width = (bitmap_ref.width / 3) as usize;
        let height = bitmap_ref.rows as usize;
        let pitch = bitmap_ref.pitch.unsigned_abs() as usize;
        let mut bitmap = Vec::with_capacity(visual_width * height * 3);
        for y in 0..height {
            let row = std::slice::from_raw_parts(bitmap_ref.buffer.add(y * pitch), pitch);
            for x in 0..visual_width {
                let idx = x * 3;
                bitmap.push(*row.get(idx).unwrap_or(&0));
                bitmap.push(*row.get(idx + 1).unwrap_or(&0));
                bitmap.push(*row.get(idx + 2).unwrap_or(&0));
            }
        }
        let ymin = (*slot).bitmap_top - bitmap_ref.rows as c_int;
        let metrics = Metrics {
            xmin: (*slot).bitmap_left,
            ymin,
            width: visual_width,
            height,
            advance_width: ((*slot).advance.x as f32 / 64.0).round(),
            advance_height: ((*slot).advance.y as f32 / 64.0).round(),
            bounds: OutlineBounds {
                xmin: (*slot).bitmap_left as f32,
                ymin: ymin as f32,
                width: visual_width as f32,
                height: height as f32,
            },
        };
        Some(GlyphSlot { metrics, bitmap })
    }
}

/// Return a metric field for an owned glyph snapshot. Fields:
///   0 = width (px)
///   1 = height (px)
///   2 = advance (px, rounded)
///   3 = bearing_x (px, rounded)
///   4 = bitmap ymin/bottom offset (px, rounded)
#[no_mangle]
pub extern "C" fn rt_fonts_glyph_metric(handle: i64, field: i64) -> i64 {
    let glyph = match glyph_from_handle(handle) {
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
    let settings = LayoutSettings {
        x: 0.0,
        y: 0.0,
        max_width: if max_width_px > 0 {
            Some(max_width_px as f32)
        } else {
            None
        },
        ..Default::default()
    };
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

/// Return the alpha coverage (0..=255) for pixel (x,y) in an owned glyph
/// snapshot. Out-of-bounds reads return 0.
#[no_mangle]
pub extern "C" fn rt_fonts_glyph_pixel(handle: i64, x: i64, y: i64) -> i64 {
    if x < 0 || y < 0 {
        return 0;
    }
    let glyph = match glyph_from_handle(handle) {
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
    if x < 0 || y < 0 || !(0..=2).contains(&channel) {
        return 0;
    }
    let glyph = match glyph_from_handle(handle) {
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

    static TEST_LOCK: Mutex<()> = Mutex::new(());
    const OWNED_TEST_FONT: &str = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../vendor/sctk-adwaita/src/title/Cantarell-Regular.ttf"
    );
    const OWNED_DEMO_FONT: &[u8] = include_bytes!(
        "../../vendor/ttf-parser/tests/fonts/demo.ttf"
    );

    fn init_owned_test_font() {
        assert!(std::path::Path::new(OWNED_TEST_FONT).exists());
        assert_eq!(
            rt_fonts_init(OWNED_TEST_FONT.as_ptr() as i64, OWNED_TEST_FONT.len() as i64),
            1
        );
    }

    fn init_owned_kern_test_font() {
        let mut source = OWNED_DEMO_FONT.to_vec();
        source[4..12].copy_from_slice(&[0, 8, 0, 128, 0, 3, 0, 0]);
        for index in 0..7 {
            let offset_pos = 12 + index * 16 + 8;
            let offset = u32::from_be_bytes(source[offset_pos..offset_pos + 4].try_into().unwrap()) + 16;
            source[offset_pos..offset_pos + 4].copy_from_slice(&offset.to_be_bytes());
        }
        let kern_directory = [
            b'k', b'e', b'r', b'n', 0, 8, 255, 215, 0, 0, 1, 160, 0, 0, 0, 24,
        ];
        let kern_table = [
            0, 0, 0, 1, 0, 0, 0, 20, 0, 1, 0, 1, 0, 6, 0, 0, 0, 0, 0, 1, 0, 1, 255, 192,
        ];
        let mut font = Vec::with_capacity(source.len() + kern_directory.len() + kern_table.len());
        font.extend_from_slice(&source[..92]);
        font.extend_from_slice(&kern_directory);
        font.extend_from_slice(&source[92..]);
        font.extend_from_slice(&kern_table);
        let path = std::env::temp_dir().join(format!("simple-owned-kern-{}.ttf", std::process::id()));
        std::fs::write(&path, font).unwrap();
        let path = path.to_str().unwrap();
        assert_eq!(rt_fonts_init(path.as_ptr() as i64, path.len() as i64), 1);
    }

    #[test]
    fn horizontal_kern_rejects_invalid_inputs() {
        let _guard = TEST_LOCK.lock().unwrap();
        assert_eq!(rt_fonts_horizontal_kern('A' as i64, 'V' as i64, 0), 0);
        assert_eq!(rt_fonts_horizontal_kern(-1, 'V' as i64, 16), 0);
    }

    #[test]
    fn horizontal_kern_returns_owned_font_pair_adjustment() {
        let _guard = TEST_LOCK.lock().unwrap();
        init_owned_kern_test_font();
        assert!(rt_fonts_horizontal_kern('A' as i64, 'A' as i64, 32) < 0);
    }

    #[test]
    fn horizontal_line_metrics_return_scaled_values() {
        let _guard = TEST_LOCK.lock().unwrap();
        init_owned_test_font();
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
    fn glyph_bearings_reconstruct_positive_y_down_layout_origin() {
        let _guard = TEST_LOCK.lock().unwrap();
        init_owned_test_font();
        let text = "G";
        assert_eq!(rt_fonts_layout_text(text.as_ptr() as i64, text.len() as i64, 16, 0), 1);
        let glyph = rt_fonts_rasterize_glyph('G' as i64, 16);
        assert!(glyph > 0);
        let ascent = rt_fonts_horizontal_line_metric(16, 0);
        let height = rt_fonts_glyph_metric(glyph, 1);
        let bearing_x = rt_fonts_glyph_metric(glyph, 3);
        let bottom = rt_fonts_glyph_metric(glyph, 4);
        assert_eq!(rt_fonts_layout_glyph_metric(0, 1), bearing_x);
        assert_eq!(rt_fonts_layout_glyph_metric(0, 2), ascent - bottom - height);
        assert_eq!(rt_fonts_glyph_free(glyph), 1);
    }

    #[test]
    fn layout_text_returns_positioned_glyphs() {
        let _guard = TEST_LOCK.lock().unwrap();
        init_owned_test_font();
        let text = "Google search deterministic compatibility fixture";
        let count = rt_fonts_layout_text(text.as_ptr() as i64, text.len() as i64, 16, 112);
        assert!(count > 0, "expected positioned glyphs, got {count}");
        assert_eq!(rt_fonts_layout_glyph_metric(0, 0), 'G' as i64);
        assert_eq!(rt_fonts_layout_glyph_metric(0, 1), 1);
        assert!(rt_fonts_layout_glyph_metric(0, 4) > 0);
        assert_eq!(rt_fonts_layout_text(0, text.len() as i64, 16, 112), -1);
    }

    #[test]
    fn subpixel_rasterize_returns_rgb_triplet_coverage() {
        let _guard = TEST_LOCK.lock().unwrap();
        init_owned_test_font();
        let handle = rt_fonts_rasterize_glyph_subpixel('G' as i64, 16);
        assert!(handle > 0);
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
        assert_eq!(rt_fonts_glyph_free(handle), 1);
    }

    #[test]
    fn glyph_metric_field_four_is_hinted_bitmap_bottom_offset() {
        let _guard = TEST_LOCK.lock().unwrap();
        init_owned_test_font();
        let handle = rt_fonts_rasterize_glyph('G' as i64, 16);
        assert!(handle > 0);
        assert_eq!(rt_fonts_glyph_metric(handle, 4), -1);
        assert_eq!(rt_fonts_glyph_free(handle), 1);
    }

    #[test]
    fn native_only_miss_does_not_hide_legacy_raster_success() {
        let _guard = TEST_LOCK.lock().unwrap();
        init_owned_test_font();
        let native_face = FREETYPE_SLOT.lock().unwrap().take();
        let native_miss = rt_fonts_rasterize_glyph_native_only('A' as i64, 16);
        let legacy = rt_fonts_rasterize_glyph('A' as i64, 16);
        *FREETYPE_SLOT.lock().unwrap() = native_face;
        assert_eq!(native_miss, 0);
        assert!(legacy > 0);
        assert_eq!(rt_fonts_glyph_free(legacy), 1);
    }

    #[test]
    fn rasterized_glyph_handles_keep_independent_snapshots() {
        let _guard = TEST_LOCK.lock().unwrap();
        init_owned_test_font();
        let first = rt_fonts_rasterize_glyph('A' as i64, 16);
        let first_width = rt_fonts_glyph_metric(first, 0);
        let second = rt_fonts_rasterize_glyph('G' as i64, 24);
        assert!(first > 0 && second > 0 && first != second);
        assert_eq!(rt_fonts_glyph_metric(first, 0), first_width);
        assert!(rt_fonts_glyph_pixels_len(first) > 0);
        assert!(rt_fonts_glyph_pixels_len(second) > 0);
        assert_eq!(rt_fonts_glyph_free(first), 1);
        assert_eq!(rt_fonts_glyph_free(second), 1);
    }

    #[test]
    fn verified_bytes_init_owns_memory_and_preserves_prior_state_on_failure() {
        let _guard = TEST_LOCK.lock().unwrap();
        let expected = lowercase_sha256_hex(OWNED_DEMO_FONT);
        assert_eq!(rt_fonts_init_verified_bytes(0, 1, expected.as_ptr() as i64, 64), 0);
        assert_eq!(rt_fonts_init_verified_bytes(1, 0, expected.as_ptr() as i64, 64), 0);
        assert_eq!(
            rt_fonts_init_verified_bytes(1, MAX_VERIFIED_FONT_BYTES + 1, expected.as_ptr() as i64, 64),
            0
        );
        assert_eq!(rt_fonts_init_verified_bytes(1, 1, 0, 64), 0);
        assert_eq!(
            rt_fonts_init_verified_bytes(
                OWNED_DEMO_FONT.as_ptr() as i64,
                OWNED_DEMO_FONT.len() as i64,
                expected.as_ptr() as i64,
                63,
            ),
            0
        );

        let mut caller_bytes = OWNED_DEMO_FONT.to_vec();
        let before = rt_fonts_generation();
        assert_eq!(
            rt_fonts_init_verified_bytes(
                caller_bytes.as_ptr() as i64,
                caller_bytes.len() as i64,
                expected.as_ptr() as i64,
                expected.len() as i64,
            ),
            1
        );
        assert_eq!(rt_fonts_generation(), before + 1);
        caller_bytes.fill(0);
        drop(caller_bytes);
        let handle = rt_fonts_rasterize_glyph('A' as i64, 16);
        assert!(handle > 0);
        assert!(rt_fonts_glyph_pixels_len(handle) > 0);
        assert_eq!(rt_fonts_glyph_free(handle), 1);
        let subpixel = rt_fonts_rasterize_glyph_subpixel('A' as i64, 16);
        assert!(subpixel > 0);
        assert!(rt_fonts_glyph_pixels_len(subpixel) > 0);
        assert_eq!(rt_fonts_glyph_free(subpixel), 1);

        let generation = rt_fonts_generation();
        let mut wrong_lowercase = expected.as_bytes().to_vec();
        wrong_lowercase[0] = if wrong_lowercase[0] == b'0' { b'1' } else { b'0' };
        assert_eq!(
            rt_fonts_init_verified_bytes(
                OWNED_DEMO_FONT.as_ptr() as i64,
                OWNED_DEMO_FONT.len() as i64,
                wrong_lowercase.as_ptr() as i64,
                wrong_lowercase.len() as i64,
            ),
            0
        );
        assert_eq!(rt_fonts_generation(), generation);
        let digest_preserved = rt_fonts_rasterize_glyph('A' as i64, 16);
        assert!(digest_preserved > 0);
        assert_eq!(rt_fonts_glyph_free(digest_preserved), 1);
        let uppercase = expected.to_uppercase();
        assert_eq!(
            rt_fonts_init_verified_bytes(
                OWNED_DEMO_FONT.as_ptr() as i64,
                OWNED_DEMO_FONT.len() as i64,
                uppercase.as_ptr() as i64,
                uppercase.len() as i64,
            ),
            0
        );
        let invalid_font = vec![0u8; 32];
        let invalid_digest = lowercase_sha256_hex(&invalid_font);
        assert_eq!(
            rt_fonts_init_verified_bytes(
                invalid_font.as_ptr() as i64,
                invalid_font.len() as i64,
                invalid_digest.as_ptr() as i64,
                invalid_digest.len() as i64,
            ),
            0
        );
        assert_eq!(rt_fonts_generation(), generation);
        let preserved = rt_fonts_rasterize_glyph('A' as i64, 16);
        assert!(preserved > 0);
        assert_eq!(rt_fonts_glyph_free(preserved), 1);
    }
}
