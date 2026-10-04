//! `rt_font_*` font SFFI for the interpreter (`simple run`).
//!
//! The C font runtime (`src/runtime/runtime_font.c`, stb_truetype) hands out
//! raw `FontData*` / `BitmapData*` pointers as `i64`. Compiled code keeps that
//! contract, but the interpreter must never let Simple code hold a raw
//! pointer: a stale, forged or double-freed value would be a use-after-free.
//! So every pointer the C side returns is parked in a handle table here and
//! Simple only ever sees an opaque, generation-checked handle:
//!
//! * handle = `(generation << SLOT_BITS) | (slot + 1)`, always > 0;
//! * freeing a handle removes it from the table and bumps the slot's
//!   generation, so the old value (and any copy of it) is rejected forever
//!   after - a double free or use-after-free returns a semantic error and
//!   never reaches C;
//! * an unknown or forged handle is rejected the same way.
//!
//! 0 keeps its C meaning ("no font" / "no bitmap") for load and glyph results.

use super::gpu::{arg_i64, arg_text};
use crate::error::CompileError;
use crate::value::Value;
use std::ffi::CString;
use std::sync::Mutex;

unsafe extern "C" {
    fn rt_font_load(path: *const std::os::raw::c_char) -> i64;
    fn rt_font_free(handle: i64);
    fn rt_font_glyph_bitmap(font_handle: i64, codepoint: i64, size: f64) -> i64;
    fn rt_font_glyph_index(font_handle: i64, codepoint: i64) -> i64;
    fn rt_font_bitmap_width(bitmap_handle: i64) -> i64;
    fn rt_font_bitmap_height(bitmap_handle: i64) -> i64;
    fn rt_font_bitmap_get_pixel(bitmap_handle: i64, x: i64, y: i64) -> i64;
    fn rt_font_bitmap_free(bitmap_handle: i64);
    fn rt_font_glyph_advance(font_handle: i64, codepoint: i64, size: f64) -> i64;
    fn rt_font_line_height(font_handle: i64, size: f64) -> i64;
    fn rt_font_ascent(font_handle: i64, size: f64) -> i64;
}

const SLOT_BITS: u32 = 24;
const SLOT_MASK: i64 = (1 << SLOT_BITS) - 1;
const MAX_GENERATION: u64 = (1 << (62 - SLOT_BITS)) - 1;

/// A table of live raw C pointers keyed by opaque generation-checked handles.
pub(crate) struct HandleTable {
    raw: Vec<i64>,
    generation: Vec<u64>,
    live: Vec<bool>,
    free_slots: Vec<usize>,
}

impl HandleTable {
    pub(crate) const fn new() -> Self {
        Self { raw: Vec::new(), generation: Vec::new(), live: Vec::new(), free_slots: Vec::new() }
    }

    /// Park a non-null raw pointer; returns its handle (0 for a null pointer
    /// or when the table is exhausted, which C callers read as "failed").
    pub(crate) fn insert(&mut self, raw: i64) -> i64 {
        if raw == 0 {
            return 0;
        }
        let slot = if let Some(slot) = self.free_slots.pop() {
            slot
        } else {
            if self.raw.len() as i64 >= SLOT_MASK {
                return 0;
            }
            self.raw.push(0);
            self.generation.push(1);
            self.live.push(false);
            self.raw.len() - 1
        };
        self.raw[slot] = raw;
        self.live[slot] = true;
        ((self.generation[slot] as i64) << SLOT_BITS) | (slot as i64 + 1)
    }

    fn decode(&self, handle: i64) -> Option<usize> {
        if handle <= 0 {
            return None;
        }
        let slot = ((handle & SLOT_MASK) - 1) as usize;
        let generation = (handle >> SLOT_BITS) as u64;
        if slot < self.raw.len() && self.live[slot] && self.generation[slot] == generation {
            Some(slot)
        } else {
            None
        }
    }

    /// The raw pointer behind a live handle.
    pub(crate) fn get(&self, handle: i64) -> Option<i64> {
        self.decode(handle).map(|slot| self.raw[slot])
    }

    /// Remove a live handle, returning its raw pointer exactly once. The slot
    /// generation is bumped so every copy of the old handle stays invalid; a
    /// slot whose generation space is exhausted is retired, never reused.
    pub(crate) fn remove(&mut self, handle: i64) -> Option<i64> {
        let slot = self.decode(handle)?;
        let raw = self.raw[slot];
        self.raw[slot] = 0;
        self.live[slot] = false;
        if self.generation[slot] < MAX_GENERATION {
            self.generation[slot] += 1;
            self.free_slots.push(slot);
        }
        Some(raw)
    }
}

static FONTS: Mutex<HandleTable> = Mutex::new(HandleTable::new());
static BITMAPS: Mutex<HandleTable> = Mutex::new(HandleTable::new());

fn table(t: &'static Mutex<HandleTable>) -> std::sync::MutexGuard<'static, HandleTable> {
    // A poisoned table still holds consistent data (every mutation is a
    // single assignment sequence without panics in between).
    t.lock().unwrap_or_else(|poisoned| poisoned.into_inner())
}

fn stale(name: &str, what: &str, handle: i64) -> CompileError {
    CompileError::semantic(format!(
        "{name}: {what} handle {handle} is not live (freed, never issued, or forged)"
    ))
}

fn font_raw(name: &str, handle: i64) -> Result<i64, CompileError> {
    table(&FONTS).get(handle).ok_or_else(|| stale(name, "font", handle))
}

fn bitmap_raw(name: &str, handle: i64) -> Result<i64, CompileError> {
    table(&BITMAPS).get(handle).ok_or_else(|| stale(name, "bitmap", handle))
}

fn arg_f64(args: &[Value], index: usize, name: &str) -> Result<f64, CompileError> {
    match args.get(index) {
        Some(Value::Float(v)) => Ok(*v),
        #[allow(clippy::cast_precision_loss)]
        Some(Value::Int(v)) => Ok(*v as f64),
        other => Err(CompileError::semantic(format!(
            "{name}: argument {index} must be a number, got {other:?}"
        ))),
    }
}

/// Register a raw `FontData*` from the C loader; used by `rt_font_load_array`.
pub(crate) fn font_handle_for_raw(raw: i64) -> i64 {
    let handle = table(&FONTS).insert(raw);
    if raw != 0 && handle == 0 {
        // Table exhausted: do not leak the C allocation.
        unsafe { rt_font_free(raw) };
    }
    handle
}

pub fn rt_font_load_fn(args: &[Value]) -> Result<Value, CompileError> {
    let path = arg_text(args, 0, "rt_font_load", 1)?;
    let Ok(c_path) = CString::new(path) else {
        return Ok(Value::Int(0));
    };
    let raw = unsafe { rt_font_load(c_path.as_ptr()) };
    Ok(Value::Int(font_handle_for_raw(raw)))
}

pub fn rt_font_free_fn(args: &[Value]) -> Result<Value, CompileError> {
    let handle = arg_i64(args, 0, "rt_font_free", 1)?;
    if handle == 0 {
        return Ok(Value::Nil);
    }
    let raw = table(&FONTS).remove(handle).ok_or_else(|| stale("rt_font_free", "font", handle))?;
    unsafe { rt_font_free(raw) };
    Ok(Value::Nil)
}

pub fn rt_font_glyph_index_fn(args: &[Value]) -> Result<Value, CompileError> {
    let font = font_raw("rt_font_glyph_index", arg_i64(args, 0, "rt_font_glyph_index", 2)?)?;
    let codepoint = arg_i64(args, 1, "rt_font_glyph_index", 2)?;
    Ok(Value::Int(unsafe { rt_font_glyph_index(font, codepoint) }))
}

pub fn rt_font_glyph_bitmap_fn(args: &[Value]) -> Result<Value, CompileError> {
    let font = font_raw("rt_font_glyph_bitmap", arg_i64(args, 0, "rt_font_glyph_bitmap", 3)?)?;
    let codepoint = arg_i64(args, 1, "rt_font_glyph_bitmap", 3)?;
    let size = arg_f64(args, 2, "rt_font_glyph_bitmap")?;
    let raw = unsafe { rt_font_glyph_bitmap(font, codepoint, size) };
    let handle = table(&BITMAPS).insert(raw);
    if raw != 0 && handle == 0 {
        // Table exhausted: do not leak the C allocation.
        unsafe { rt_font_bitmap_free(raw) };
    }
    Ok(Value::Int(handle))
}

pub fn rt_font_glyph_advance_fn(args: &[Value]) -> Result<Value, CompileError> {
    let font = font_raw("rt_font_glyph_advance", arg_i64(args, 0, "rt_font_glyph_advance", 3)?)?;
    let codepoint = arg_i64(args, 1, "rt_font_glyph_advance", 3)?;
    let size = arg_f64(args, 2, "rt_font_glyph_advance")?;
    Ok(Value::Int(unsafe { rt_font_glyph_advance(font, codepoint, size) }))
}

pub fn rt_font_line_height_fn(args: &[Value]) -> Result<Value, CompileError> {
    let font = font_raw("rt_font_line_height", arg_i64(args, 0, "rt_font_line_height", 2)?)?;
    let size = arg_f64(args, 1, "rt_font_line_height")?;
    Ok(Value::Int(unsafe { rt_font_line_height(font, size) }))
}

pub fn rt_font_ascent_fn(args: &[Value]) -> Result<Value, CompileError> {
    let font = font_raw("rt_font_ascent", arg_i64(args, 0, "rt_font_ascent", 2)?)?;
    let size = arg_f64(args, 1, "rt_font_ascent")?;
    Ok(Value::Int(unsafe { rt_font_ascent(font, size) }))
}

pub fn rt_font_bitmap_width_fn(args: &[Value]) -> Result<Value, CompileError> {
    let bitmap = bitmap_raw("rt_font_bitmap_width", arg_i64(args, 0, "rt_font_bitmap_width", 1)?)?;
    Ok(Value::Int(unsafe { rt_font_bitmap_width(bitmap) }))
}

pub fn rt_font_bitmap_height_fn(args: &[Value]) -> Result<Value, CompileError> {
    let bitmap = bitmap_raw("rt_font_bitmap_height", arg_i64(args, 0, "rt_font_bitmap_height", 1)?)?;
    Ok(Value::Int(unsafe { rt_font_bitmap_height(bitmap) }))
}

pub fn rt_font_bitmap_get_pixel_fn(args: &[Value]) -> Result<Value, CompileError> {
    let bitmap = bitmap_raw(
        "rt_font_bitmap_get_pixel",
        arg_i64(args, 0, "rt_font_bitmap_get_pixel", 3)?,
    )?;
    let x = arg_i64(args, 1, "rt_font_bitmap_get_pixel", 3)?;
    let y = arg_i64(args, 2, "rt_font_bitmap_get_pixel", 3)?;
    // runtime_font.c bounds-checks x/y against the bitmap and answers 0.
    Ok(Value::Int(unsafe { rt_font_bitmap_get_pixel(bitmap, x, y) }))
}

pub fn rt_font_bitmap_free_fn(args: &[Value]) -> Result<Value, CompileError> {
    let handle = arg_i64(args, 0, "rt_font_bitmap_free", 1)?;
    if handle == 0 {
        return Ok(Value::Nil);
    }
    let raw = table(&BITMAPS)
        .remove(handle)
        .ok_or_else(|| stale("rt_font_bitmap_free", "bitmap", handle))?;
    unsafe { rt_font_bitmap_free(raw) };
    Ok(Value::Nil)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn handle_table_rejects_use_after_free_and_double_free() {
        let mut t = HandleTable::new();
        let h = t.insert(0x1000);
        assert!(h > 0);
        assert_eq!(t.get(h), Some(0x1000));
        assert_eq!(t.remove(h), Some(0x1000));
        assert_eq!(t.get(h), None, "use after free must be rejected");
        assert_eq!(t.remove(h), None, "double free must be rejected");
    }

    #[test]
    fn handle_table_reused_slot_does_not_revive_old_handle() {
        let mut t = HandleTable::new();
        let old = t.insert(0x1000);
        t.remove(old);
        let new = t.insert(0x2000);
        assert_ne!(old, new);
        assert_eq!(old & SLOT_MASK, new & SLOT_MASK, "slot is reused");
        assert_eq!(t.get(old), None);
        assert_eq!(t.get(new), Some(0x2000));
    }

    #[test]
    fn handle_table_rejects_forged_and_raw_values() {
        let mut t = HandleTable::new();
        let h = t.insert(0x1000);
        assert_eq!(t.get(0), None);
        assert_eq!(t.get(-5), None);
        assert_eq!(t.get(0x1000), None, "a raw pointer value is not a handle");
        assert_eq!(t.get(h + 1), None);
        assert_eq!(t.get(h + (1 << SLOT_BITS)), None, "wrong generation");
        assert_eq!(t.insert(0), 0, "null pointer is never registered");
    }

    #[test]
    fn font_externs_return_errors_not_ub_for_dead_handles() {
        let forged = 0x7fff_0000_0001_i64;
        assert!(rt_font_glyph_index_fn(&[Value::Int(forged), Value::Int(65)]).is_err());
        assert!(rt_font_free_fn(&[Value::Int(forged)]).is_err());
        assert!(rt_font_bitmap_width_fn(&[Value::Int(forged)]).is_err());
        assert!(rt_font_bitmap_free_fn(&[Value::Int(forged)]).is_err());
        assert!(rt_font_free_fn(&[Value::Int(0)]).is_ok(), "free(0) is a no-op");
    }

    #[test]
    fn font_load_missing_path_returns_zero() {
        let r = rt_font_load_fn(&[Value::text("/nonexistent/simple-font-test.ttf".to_string())]).unwrap();
        assert!(matches!(r, Value::Int(0)));
    }

    fn int(v: Value) -> i64 {
        match v {
            Value::Int(i) => i,
            other => panic!("expected Int, got {other:?}"),
        }
    }

    #[test]
    fn real_font_roundtrip_then_dead_handles_error() {
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../../assets/fonts/google-fonts/ofl/bungee/Bungee-Regular.ttf");
        let font = int(rt_font_load_fn(&[Value::text(path.to_string())]).unwrap());
        assert!(font > 0, "font loads through the handle table");
        let glyph = int(rt_font_glyph_index_fn(&[Value::Int(font), Value::Int('A' as i64)]).unwrap());
        assert!(glyph > 0);
        assert!(int(rt_font_line_height_fn(&[Value::Int(font), Value::Float(16.0)]).unwrap()) > 0);
        let bmp = int(rt_font_glyph_bitmap_fn(&[Value::Int(font), Value::Int('A' as i64), Value::Float(24.0)]).unwrap());
        assert!(bmp > 0);
        let w = int(rt_font_bitmap_width_fn(&[Value::Int(bmp)]).unwrap());
        assert!(w > 0);
        // Out-of-bounds pixel reads are clamped to 0 by the C side.
        assert_eq!(int(rt_font_bitmap_get_pixel_fn(&[Value::Int(bmp), Value::Int(w + 5), Value::Int(0)]).unwrap()), 0);
        assert!(rt_font_bitmap_free_fn(&[Value::Int(bmp)]).is_ok());
        assert!(rt_font_bitmap_width_fn(&[Value::Int(bmp)]).is_err(), "bitmap use after free");
        assert!(rt_font_bitmap_free_fn(&[Value::Int(bmp)]).is_err(), "bitmap double free");
        assert!(rt_font_free_fn(&[Value::Int(font)]).is_ok());
        assert!(rt_font_glyph_index_fn(&[Value::Int(font), Value::Int(65)]).is_err(), "font use after free");
        assert!(rt_font_free_fn(&[Value::Int(font)]).is_err(), "font double free");
    }
}
