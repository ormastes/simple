//! Minimal FFI for UI primitives
//!
//! This module provides low-level FFI functions for TUI/GUI rendering
//! that are not already covered by the terminal module in Simple stdlib.
//!
//! Most UI functionality is implemented in Simple at `simple/std_lib/src/ui/`.
//! This FFI module only provides primitives that require Rust/native code.

use std::io::{self, Write};

/// Screen buffer for double-buffered rendering (avoids flickering)
pub struct ScreenBuffer {
    width: usize,
    height: usize,
    cells: Vec<Cell>,
    dirty: Vec<bool>,
}

/// A single cell in the screen buffer
#[derive(Clone, Default)]
pub struct Cell {
    pub ch: char,
    pub fg: u32,  // RGBA color
    pub bg: u32,  // RGBA color
    pub flags: u8, // bold=1, dim=2, italic=4, underline=8, blink=16, reverse=32
}

impl ScreenBuffer {
    pub fn new(width: usize, height: usize) -> Self {
        let size = width * height;
        Self {
            width,
            height,
            cells: vec![Cell::default(); size],
            dirty: vec![false; size],
        }
    }

    pub fn resize(&mut self, width: usize, height: usize) {
        let size = width * height;
        self.width = width;
        self.height = height;
        self.cells.resize(size, Cell::default());
        self.dirty.resize(size, false);
        self.dirty.fill(true); // Mark all as dirty after resize
    }

    pub fn set_cell(&mut self, x: usize, y: usize, cell: Cell) {
        if x < self.width && y < self.height {
            let idx = y * self.width + x;
            if self.cells[idx].ch != cell.ch
                || self.cells[idx].fg != cell.fg
                || self.cells[idx].bg != cell.bg
                || self.cells[idx].flags != cell.flags
            {
                self.cells[idx] = cell;
                self.dirty[idx] = true;
            }
        }
    }

    pub fn get_cell(&self, x: usize, y: usize) -> Option<&Cell> {
        if x < self.width && y < self.height {
            Some(&self.cells[y * self.width + x])
        } else {
            None
        }
    }

    /// Flush only dirty cells to terminal
    pub fn flush(&mut self, writer: &mut dyn Write) -> io::Result<()> {
        for y in 0..self.height {
            for x in 0..self.width {
                let idx = y * self.width + x;
                if self.dirty[idx] {
                    let cell = &self.cells[idx];
                    // Move cursor
                    write!(writer, "\x1b[{};{}H", y + 1, x + 1)?;
                    // Apply styles
                    write_cell_style(writer, cell)?;
                    // Write character
                    write!(writer, "{}", cell.ch)?;
                    self.dirty[idx] = false;
                }
            }
        }
        writer.flush()
    }

    /// Clear all dirty flags
    pub fn clear_dirty(&mut self) {
        self.dirty.fill(false);
    }

    /// Mark all cells as dirty (for full redraw)
    pub fn mark_all_dirty(&mut self) {
        self.dirty.fill(true);
    }
}

fn write_cell_style(writer: &mut dyn Write, cell: &Cell) -> io::Result<()> {
    let mut codes = Vec::new();

    // Flags
    if cell.flags & 1 != 0 { codes.push("1".to_string()); } // bold
    if cell.flags & 2 != 0 { codes.push("2".to_string()); } // dim
    if cell.flags & 4 != 0 { codes.push("3".to_string()); } // italic
    if cell.flags & 8 != 0 { codes.push("4".to_string()); } // underline
    if cell.flags & 16 != 0 { codes.push("5".to_string()); } // blink
    if cell.flags & 32 != 0 { codes.push("7".to_string()); } // reverse

    // Foreground color (RGB)
    if cell.fg != 0 {
        let r = (cell.fg >> 16) & 0xFF;
        let g = (cell.fg >> 8) & 0xFF;
        let b = cell.fg & 0xFF;
        codes.push(format!("38;2;{};{};{}", r, g, b));
    }

    // Background color (RGB)
    if cell.bg != 0 {
        let r = (cell.bg >> 16) & 0xFF;
        let g = (cell.bg >> 8) & 0xFF;
        let b = cell.bg & 0xFF;
        codes.push(format!("48;2;{};{};{}", r, g, b));
    }

    if !codes.is_empty() {
        write!(writer, "\x1b[0;{}m", codes.join(";"))?;
    } else {
        write!(writer, "\x1b[0m")?;
    }
    Ok(())
}

// FFI exports for Simple language

/// Create a new screen buffer
#[no_mangle]
pub extern "C" fn ui_screen_buffer_new(width: u32, height: u32) -> *mut ScreenBuffer {
    Box::into_raw(Box::new(ScreenBuffer::new(width as usize, height as usize)))
}

/// Free a screen buffer
#[no_mangle]
pub extern "C" fn ui_screen_buffer_free(buf: *mut ScreenBuffer) {
    if !buf.is_null() {
        unsafe { drop(Box::from_raw(buf)) };
    }
}

/// Resize screen buffer
#[no_mangle]
pub extern "C" fn ui_screen_buffer_resize(buf: *mut ScreenBuffer, width: u32, height: u32) {
    if !buf.is_null() {
        unsafe { (*buf).resize(width as usize, height as usize) };
    }
}

/// Set a cell in the screen buffer
#[no_mangle]
pub extern "C" fn ui_screen_buffer_set_cell(
    buf: *mut ScreenBuffer,
    x: u32,
    y: u32,
    ch: u32,
    fg: u32,
    bg: u32,
    flags: u8,
) {
    if !buf.is_null() {
        let cell = Cell {
            ch: char::from_u32(ch).unwrap_or(' '),
            fg,
            bg,
            flags,
        };
        unsafe { (*buf).set_cell(x as usize, y as usize, cell) };
    }
}

/// Flush dirty cells to stdout
#[no_mangle]
pub extern "C" fn ui_screen_buffer_flush(buf: *mut ScreenBuffer) -> i32 {
    if buf.is_null() {
        return -1;
    }
    let mut stdout = io::stdout();
    match unsafe { (*buf).flush(&mut stdout) } {
        Ok(()) => 0,
        Err(_) => -1,
    }
}

/// Mark all cells as dirty
#[no_mangle]
pub extern "C" fn ui_screen_buffer_mark_dirty(buf: *mut ScreenBuffer) {
    if !buf.is_null() {
        unsafe { (*buf).mark_all_dirty() };
    }
}

// =============================================================================
// Native Window FFI (GUI Renderer)
// =============================================================================

/// Native window handle for GUI rendering
pub struct NativeWindow {
    width: u32,
    height: u32,
    framebuffer: Vec<u32>,  // RGBA pixels
    title: String,
    // In a real implementation, this would hold the platform window handle
    // (HWND on Windows, NSWindow on macOS, X11 Window on Linux)
}

impl NativeWindow {
    pub fn new(width: u32, height: u32, title: &str) -> Self {
        Self {
            width,
            height,
            framebuffer: vec![0; (width * height) as usize],
            title: title.to_string(),
        }
    }

    pub fn resize(&mut self, width: u32, height: u32) {
        self.width = width;
        self.height = height;
        self.framebuffer.resize((width * height) as usize, 0);
    }

    pub fn width(&self) -> u32 {
        self.width
    }

    pub fn height(&self) -> u32 {
        self.height
    }

    pub fn set_pixel(&mut self, x: u32, y: u32, color: u32) {
        if x < self.width && y < self.height {
            self.framebuffer[(y * self.width + x) as usize] = color;
        }
    }

    pub fn fill_rect(&mut self, x: u32, y: u32, w: u32, h: u32, color: u32) {
        for dy in 0..h {
            for dx in 0..w {
                self.set_pixel(x + dx, y + dy, color);
            }
        }
    }

    pub fn get_framebuffer(&self) -> &[u32] {
        &self.framebuffer
    }
}

/// Create a native window
#[no_mangle]
pub extern "C" fn ui_native_window_create(
    width: u32,
    height: u32,
    title_ptr: *const u8,
    title_len: usize,
) -> *mut NativeWindow {
    let title = if title_ptr.is_null() || title_len == 0 {
        "Simple UI".to_string()
    } else {
        unsafe {
            let slice = std::slice::from_raw_parts(title_ptr, title_len);
            String::from_utf8_lossy(slice).to_string()
        }
    };
    Box::into_raw(Box::new(NativeWindow::new(width, height, &title)))
}

/// Free a native window
#[no_mangle]
pub extern "C" fn ui_native_window_free(win: *mut NativeWindow) {
    if !win.is_null() {
        unsafe { drop(Box::from_raw(win)) };
    }
}

/// Resize native window
#[no_mangle]
pub extern "C" fn ui_native_window_resize(win: *mut NativeWindow, width: u32, height: u32) {
    if !win.is_null() {
        unsafe { (*win).resize(width, height) };
    }
}

/// Get window width
#[no_mangle]
pub extern "C" fn ui_native_window_width(win: *const NativeWindow) -> u32 {
    if win.is_null() {
        0
    } else {
        unsafe { (*win).width() }
    }
}

/// Get window height
#[no_mangle]
pub extern "C" fn ui_native_window_height(win: *const NativeWindow) -> u32 {
    if win.is_null() {
        0
    } else {
        unsafe { (*win).height() }
    }
}

/// Set a pixel in the framebuffer
#[no_mangle]
pub extern "C" fn ui_native_window_set_pixel(
    win: *mut NativeWindow,
    x: u32,
    y: u32,
    color: u32,
) {
    if !win.is_null() {
        unsafe { (*win).set_pixel(x, y, color) };
    }
}

/// Fill a rectangle in the framebuffer
#[no_mangle]
pub extern "C" fn ui_native_window_fill_rect(
    win: *mut NativeWindow,
    x: u32,
    y: u32,
    w: u32,
    h: u32,
    color: u32,
) {
    if !win.is_null() {
        unsafe { (*win).fill_rect(x, y, w, h, color) };
    }
}

/// Get framebuffer pointer (for direct manipulation)
#[no_mangle]
pub extern "C" fn ui_native_window_framebuffer(win: *const NativeWindow) -> *const u32 {
    if win.is_null() {
        std::ptr::null()
    } else {
        unsafe { (*win).get_framebuffer().as_ptr() }
    }
}

/// Present the framebuffer (in real impl, this would swap buffers/blit to screen)
/// Returns 0 on success, -1 on error
#[no_mangle]
pub extern "C" fn ui_native_window_present(win: *mut NativeWindow) -> i32 {
    if win.is_null() {
        return -1;
    }
    // In a real implementation, this would:
    // - Windows: BitBlt to window DC
    // - macOS: Draw to NSView
    // - Linux/X11: XPutImage
    // - Wayland: Attach buffer and commit
    0
}

/// Poll for window events
/// Returns event type: 0=none, 1=close, 2=resize, 3=key, 4=mouse
#[no_mangle]
pub extern "C" fn ui_native_window_poll_event(
    _win: *mut NativeWindow,
    _event_data: *mut u64,
) -> i32 {
    // In a real implementation, this would poll the event queue
    // and fill event_data with event-specific information
    0 // No event
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_screen_buffer_create() {
        let buf = ScreenBuffer::new(80, 24);
        assert_eq!(buf.width, 80);
        assert_eq!(buf.height, 24);
        assert_eq!(buf.cells.len(), 80 * 24);
    }

    #[test]
    fn test_screen_buffer_set_cell() {
        let mut buf = ScreenBuffer::new(10, 10);
        buf.set_cell(5, 5, Cell { ch: 'X', fg: 0xFF0000, bg: 0, flags: 1 });
        let cell = buf.get_cell(5, 5).unwrap();
        assert_eq!(cell.ch, 'X');
        assert_eq!(cell.fg, 0xFF0000);
        assert!(buf.dirty[5 * 10 + 5]);
    }

    #[test]
    fn test_ffi_functions() {
        let buf = ui_screen_buffer_new(40, 20);
        assert!(!buf.is_null());
        ui_screen_buffer_set_cell(buf, 10, 10, 'A' as u32, 0xFFFFFF, 0, 0);
        ui_screen_buffer_resize(buf, 80, 24);
        ui_screen_buffer_mark_dirty(buf);
        ui_screen_buffer_free(buf);
    }

    #[test]
    fn test_native_window_create() {
        let win = NativeWindow::new(800, 600, "Test Window");
        assert_eq!(win.width, 800);
        assert_eq!(win.height, 600);
        assert_eq!(win.framebuffer.len(), 800 * 600);
    }

    #[test]
    fn test_native_window_fill_rect() {
        let mut win = NativeWindow::new(100, 100, "Test");
        win.fill_rect(10, 10, 20, 20, 0xFF0000FF);
        // Check corner pixels
        assert_eq!(win.framebuffer[10 * 100 + 10], 0xFF0000FF);
        assert_eq!(win.framebuffer[29 * 100 + 29], 0xFF0000FF);
        // Check outside
        assert_eq!(win.framebuffer[9 * 100 + 9], 0);
    }

    #[test]
    fn test_native_window_ffi() {
        let win = ui_native_window_create(640, 480, std::ptr::null(), 0);
        assert!(!win.is_null());
        assert_eq!(ui_native_window_width(win), 640);
        assert_eq!(ui_native_window_height(win), 480);
        ui_native_window_fill_rect(win, 0, 0, 100, 100, 0xFFFFFFFF);
        assert_eq!(ui_native_window_present(win), 0);
        ui_native_window_free(win);
    }
}
