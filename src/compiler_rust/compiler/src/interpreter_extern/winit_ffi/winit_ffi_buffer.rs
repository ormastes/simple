use std::sync::Arc;
use std::sync::atomic::Ordering;

use crate::error::CompileError;
use crate::value::Value;

use super::super::conversion::glyph_8x16;
use super::{
    get_i64, get_string, get_pixels, int_value, bool_value, set_last_error, NEXT_BUFFER_ID, PIXEL_BUFFERS, PixelBuffer,
    EVENT_LOOPS, WINDOW_OWNERS, RuntimeCommand,
};

#[cfg(target_os = "macos")]
use super::winit_ffi_thread::macos_pump;

pub(super) fn dispatch_buffer(name: &str, args: &[Value]) -> Result<Value, CompileError> {
    match name {
        "rt_winit_buffer_create" => {
            // rt_winit_buffer_create(width, height, fill_color) -> buffer_id
            let width = get_i64(args, 0, name)?.max(1) as u32;
            let height = get_i64(args, 1, name)?.max(1) as u32;
            let color = get_i64(args, 2, name)? as u32;
            let id = NEXT_BUFFER_ID.fetch_add(1, Ordering::Relaxed);
            let buf = PixelBuffer {
                width,
                height,
                pixels: vec![color; (width * height) as usize],
            };
            PIXEL_BUFFERS.lock().insert(id, buf);
            Ok(int_value(id))
        }
        "rt_winit_buffer_fill_rect" => {
            // rt_winit_buffer_fill_rect(buffer_id, x, y, w, h, color) -> bool
            let buf_id = get_i64(args, 0, name)?;
            let x = get_i64(args, 1, name)?;
            let y = get_i64(args, 2, name)?;
            let w = get_i64(args, 3, name)?;
            let h = get_i64(args, 4, name)?;
            let color = get_i64(args, 5, name)? as u32;
            let mut bufs = PIXEL_BUFFERS.lock();
            if let Some(buf) = bufs.get_mut(&buf_id) {
                let sw = buf.width as i64;
                let sh = buf.height as i64;
                for row in 0..h {
                    let py = y + row;
                    if py < 0 || py >= sh {
                        continue;
                    }
                    for col in 0..w {
                        let px = x + col;
                        if px < 0 || px >= sw {
                            continue;
                        }
                        buf.pixels[(py as usize) * (sw as usize) + (px as usize)] = color;
                    }
                }
                Ok(bool_value(true))
            } else {
                set_last_error(format!("invalid buffer handle: {buf_id}"));
                Ok(bool_value(false))
            }
        }
        "rt_winit_buffer_draw_text" => {
            // rt_winit_buffer_draw_text(buffer_id, x, y, text, fg, bg) -> bool
            let buf_id = get_i64(args, 0, name)?;
            let x = get_i64(args, 1, name)?;
            let y = get_i64(args, 2, name)?;
            let text = get_string(args, 3, name)?;
            let fg = get_i64(args, 4, name)? as u32;
            let bg = get_i64(args, 5, name)? as u32;
            let mut bufs = PIXEL_BUFFERS.lock();
            if let Some(buf) = bufs.get_mut(&buf_id) {
                draw_text_into_buffer(buf, x, y, &text, fg, bg);
                Ok(bool_value(true))
            } else {
                set_last_error(format!("invalid buffer handle: {buf_id}"));
                Ok(bool_value(false))
            }
        }
        "rt_winit_buffer_present" => {
            // rt_winit_buffer_present(window_id, buffer_id) -> bool
            let window_id = get_i64(args, 0, name)?;
            let buf_id = get_i64(args, 1, name)?;
            let (width, height, pixels) = {
                let bufs = PIXEL_BUFFERS.lock();
                if let Some(buf) = bufs.get(&buf_id) {
                    (buf.width, buf.height, buf.pixels.clone())
                } else {
                    set_last_error(format!("invalid buffer handle: {buf_id}"));
                    return Ok(bool_value(false));
                }
            };
            let event_loop_id = WINDOW_OWNERS.lock().get(&window_id).copied();
            if let Some(el_id) = event_loop_id {
                let (response_tx, response_rx) = crossbeam::channel::bounded(1);
                {
                    if let Some(handle) = EVENT_LOOPS.lock().get(&el_id) {
                        handle
                            .command_tx
                            .send(RuntimeCommand::Present {
                                window_id,
                                width,
                                height,
                                pixels,
                                response: response_tx,
                            })
                            .map_err(|err| super::runtime_error(format!("failed to send present: {err}")))?;
                    }
                }
                #[cfg(target_os = "macos")]
                for _ in 0..50 {
                    macos_pump(el_id);
                    if let Ok(result) = response_rx.try_recv() {
                        return match result {
                            Ok(()) => Ok(bool_value(true)),
                            Err(err) => {
                                set_last_error(err);
                                Ok(bool_value(false))
                            }
                        };
                    }
                    std::thread::sleep(std::time::Duration::from_millis(2));
                }
                return match response_rx.recv_timeout(std::time::Duration::from_secs(2)) {
                    Ok(Ok(())) => Ok(bool_value(true)),
                    Ok(Err(err)) => {
                        set_last_error(err);
                        Ok(bool_value(false))
                    }
                    Err(err) => Err(super::runtime_error(format!("present response timeout: {err}"))),
                };
            }
            set_last_error(format!("invalid window handle: {window_id}"));
            Ok(bool_value(false))
        }
        "rt_winit_buffer_save_bmp" => {
            // rt_winit_buffer_save_bmp(buffer_id, path) -> bool
            let buf_id = get_i64(args, 0, name)?;
            let path = get_string(args, 1, name)?;
            let bufs = PIXEL_BUFFERS.lock();
            if let Some(buf) = bufs.get(&buf_id) {
                let width = buf.width;
                let height = buf.height;
                let row_size = ((width * 3 + 3) / 4) * 4;
                let pixel_data_size = row_size * height;
                let file_size = 54 + pixel_data_size;
                let mut data = Vec::with_capacity(file_size as usize);

                // BMP file header
                data.extend_from_slice(b"BM");
                data.extend_from_slice(&file_size.to_le_bytes());
                data.extend_from_slice(&[0u8; 4]);
                data.extend_from_slice(&54u32.to_le_bytes());
                // DIB header
                data.extend_from_slice(&40u32.to_le_bytes());
                data.extend_from_slice(&width.to_le_bytes());
                data.extend_from_slice(&height.to_le_bytes());
                data.extend_from_slice(&1u16.to_le_bytes());
                data.extend_from_slice(&24u16.to_le_bytes());
                data.extend_from_slice(&0u32.to_le_bytes());
                data.extend_from_slice(&pixel_data_size.to_le_bytes());
                data.extend_from_slice(&2835u32.to_le_bytes());
                data.extend_from_slice(&2835u32.to_le_bytes());
                data.extend_from_slice(&0u32.to_le_bytes());
                data.extend_from_slice(&0u32.to_le_bytes());

                let pad_bytes = (row_size - width * 3) as usize;
                for y in (0..height).rev() {
                    for x in 0..width {
                        let argb = buf.pixels[(y * width + x) as usize];
                        data.push((argb & 0xFF) as u8);
                        data.push(((argb >> 8) & 0xFF) as u8);
                        data.push(((argb >> 16) & 0xFF) as u8);
                    }
                    for _ in 0..pad_bytes {
                        data.push(0);
                    }
                }

                match std::fs::write(&path, &data) {
                    Ok(()) => Ok(bool_value(true)),
                    Err(err) => {
                        set_last_error(format!("BMP write failed: {err}"));
                        Ok(bool_value(false))
                    }
                }
            } else {
                set_last_error(format!("invalid buffer handle: {buf_id}"));
                Ok(bool_value(false))
            }
        }
        "rt_winit_buffer_read_pixel" => {
            // rt_winit_buffer_read_pixel(buffer_id, x, y) -> i64 (ARGB pixel value)
            let buf_id = get_i64(args, 0, name)?;
            let x = get_i64(args, 1, name)?;
            let y = get_i64(args, 2, name)?;
            let bufs = PIXEL_BUFFERS.lock();
            if let Some(buf) = bufs.get(&buf_id) {
                let sw = buf.width as i64;
                let sh = buf.height as i64;
                if x >= 0 && x < sw && y >= 0 && y < sh {
                    let idx = (y as usize) * (sw as usize) + (x as usize);
                    Ok(int_value(buf.pixels[idx] as i64))
                } else {
                    Ok(int_value(0))
                }
            } else {
                set_last_error(format!("invalid buffer handle: {buf_id}"));
                Ok(int_value(0))
            }
        }
        "rt_winit_buffer_blend_rect" => {
            // rt_winit_buffer_blend_rect(buffer_id, x, y, w, h, color, alpha) -> bool
            let buf_id = get_i64(args, 0, name)?;
            let x = get_i64(args, 1, name)?;
            let y = get_i64(args, 2, name)?;
            let w = get_i64(args, 3, name)?;
            let h = get_i64(args, 4, name)?;
            let color = get_i64(args, 5, name)? as u32;
            let alpha = get_i64(args, 6, name)?.clamp(0, 255) as u32;
            let mut bufs = PIXEL_BUFFERS.lock();
            if let Some(buf) = bufs.get_mut(&buf_id) {
                let sw = buf.width as i64;
                let sh = buf.height as i64;
                let sr = (color >> 16) & 0xFF;
                let sg = (color >> 8) & 0xFF;
                let sb = color & 0xFF;
                let inv_alpha = 255 - alpha;
                for row in 0..h {
                    let py = y + row;
                    if py < 0 || py >= sh {
                        continue;
                    }
                    for col in 0..w {
                        let px = x + col;
                        if px < 0 || px >= sw {
                            continue;
                        }
                        let idx = (py as usize) * (sw as usize) + (px as usize);
                        let dst = buf.pixels[idx];
                        let dr = (dst >> 16) & 0xFF;
                        let dg = (dst >> 8) & 0xFF;
                        let db = dst & 0xFF;
                        let r = (sr * alpha + dr * inv_alpha) / 255;
                        let g = (sg * alpha + dg * inv_alpha) / 255;
                        let b = (sb * alpha + db * inv_alpha) / 255;
                        buf.pixels[idx] = 0xFF000000 | (r << 16) | (g << 8) | b;
                    }
                }
                Ok(bool_value(true))
            } else {
                set_last_error(format!("invalid buffer handle: {buf_id}"));
                Ok(bool_value(false))
            }
        }
        "rt_winit_buffer_blur" => {
            // rt_winit_buffer_blur(buffer_id, x, y, w, h, radius) -> bool
            let buf_id = get_i64(args, 0, name)?;
            let bx = get_i64(args, 1, name)?;
            let by = get_i64(args, 2, name)?;
            let bw = get_i64(args, 3, name)?;
            let bh = get_i64(args, 4, name)?;
            let radius = get_i64(args, 5, name)?.clamp(1, 50) as usize;
            let mut bufs = PIXEL_BUFFERS.lock();
            if let Some(buf) = bufs.get_mut(&buf_id) {
                let sw = buf.width as i64;
                let sh = buf.height as i64;
                // Clamp region
                let x0 = bx.max(0) as usize;
                let y0 = by.max(0) as usize;
                let x1 = (bx + bw).min(sw) as usize;
                let y1 = (by + bh).min(sh) as usize;
                let rw = x1.saturating_sub(x0);
                let rh = y1.saturating_sub(y0);
                if rw == 0 || rh == 0 {
                    return Ok(bool_value(true));
                }
                let stride = sw as usize;
                // 3-pass box blur approximation of Gaussian
                for _ in 0..3 {
                    // Horizontal pass
                    let mut temp = vec![0u32; rw * rh];
                    for row in 0..rh {
                        for col in 0..rw {
                            let mut r_sum: u64 = 0;
                            let mut g_sum: u64 = 0;
                            let mut b_sum: u64 = 0;
                            let mut count: u64 = 0;
                            let c_min = if col >= radius { col - radius } else { 0 };
                            let c_max = (col + radius + 1).min(rw);
                            for kc in c_min..c_max {
                                let px = buf.pixels[(y0 + row) * stride + (x0 + kc)];
                                r_sum += ((px >> 16) & 0xFF) as u64;
                                g_sum += ((px >> 8) & 0xFF) as u64;
                                b_sum += (px & 0xFF) as u64;
                                count += 1;
                            }
                            if count == 0 {
                                count = 1;
                            }
                            let r = (r_sum / count) as u32;
                            let g = (g_sum / count) as u32;
                            let b = (b_sum / count) as u32;
                            temp[row * rw + col] = 0xFF000000 | (r << 16) | (g << 8) | b;
                        }
                    }
                    // Write horizontal back
                    for row in 0..rh {
                        for col in 0..rw {
                            buf.pixels[(y0 + row) * stride + (x0 + col)] = temp[row * rw + col];
                        }
                    }
                    // Vertical pass
                    for col in 0..rw {
                        for row in 0..rh {
                            let mut r_sum: u64 = 0;
                            let mut g_sum: u64 = 0;
                            let mut b_sum: u64 = 0;
                            let mut count: u64 = 0;
                            let r_min = if row >= radius { row - radius } else { 0 };
                            let r_max = (row + radius + 1).min(rh);
                            for kr in r_min..r_max {
                                let px = buf.pixels[(y0 + kr) * stride + (x0 + col)];
                                r_sum += ((px >> 16) & 0xFF) as u64;
                                g_sum += ((px >> 8) & 0xFF) as u64;
                                b_sum += (px & 0xFF) as u64;
                                count += 1;
                            }
                            if count == 0 {
                                count = 1;
                            }
                            let r = (r_sum / count) as u32;
                            let g = (g_sum / count) as u32;
                            let b = (b_sum / count) as u32;
                            temp[row * rw + col] = 0xFF000000 | (r << 16) | (g << 8) | b;
                        }
                    }
                    // Write vertical back
                    for row in 0..rh {
                        for col in 0..rw {
                            buf.pixels[(y0 + row) * stride + (x0 + col)] = temp[row * rw + col];
                        }
                    }
                }
                Ok(bool_value(true))
            } else {
                set_last_error(format!("invalid buffer handle: {buf_id}"));
                Ok(bool_value(false))
            }
        }
        "rt_winit_buffer_gradient_v" => {
            // rt_winit_buffer_gradient_v(buffer_id, x, y, w, h, color1, color2) -> bool
            let buf_id = get_i64(args, 0, name)?;
            let gx = get_i64(args, 1, name)?;
            let gy = get_i64(args, 2, name)?;
            let gw = get_i64(args, 3, name)?;
            let gh = get_i64(args, 4, name)?;
            let c1 = get_i64(args, 5, name)? as u32;
            let c2 = get_i64(args, 6, name)? as u32;
            let mut bufs = PIXEL_BUFFERS.lock();
            if let Some(buf) = bufs.get_mut(&buf_id) {
                let sw = buf.width as i64;
                let sh = buf.height as i64;
                let r1 = ((c1 >> 16) & 0xFF) as i64;
                let g1 = ((c1 >> 8) & 0xFF) as i64;
                let b1 = (c1 & 0xFF) as i64;
                let r2 = ((c2 >> 16) & 0xFF) as i64;
                let g2 = ((c2 >> 8) & 0xFF) as i64;
                let b2 = (c2 & 0xFF) as i64;
                for row in 0..gh {
                    let py = gy + row;
                    if py < 0 || py >= sh {
                        continue;
                    }
                    let t = if gh > 1 { row as f64 / (gh - 1) as f64 } else { 0.0 };
                    let r = (r1 as f64 + (r2 - r1) as f64 * t) as u32;
                    let g = (g1 as f64 + (g2 - g1) as f64 * t) as u32;
                    let b = (b1 as f64 + (b2 - b1) as f64 * t) as u32;
                    let color = 0xFF000000 | (r << 16) | (g << 8) | b;
                    for col in 0..gw {
                        let px = gx + col;
                        if px < 0 || px >= sw {
                            continue;
                        }
                        buf.pixels[(py as usize) * (sw as usize) + (px as usize)] = color;
                    }
                }
                Ok(bool_value(true))
            } else {
                set_last_error(format!("invalid buffer handle: {buf_id}"));
                Ok(bool_value(false))
            }
        }
        "rt_winit_buffer_get_pixels" => {
            // rt_winit_buffer_get_pixels(buffer_id) -> [i64] (pixel array)
            let buf_id = get_i64(args, 0, name)?;
            let bufs = PIXEL_BUFFERS.lock();
            if let Some(buf) = bufs.get(&buf_id) {
                let values: Vec<Value> = buf.pixels.iter().map(|&p| Value::Int(p as i64)).collect();
                Ok(Value::Array(Arc::new(values)))
            } else {
                set_last_error(format!("invalid buffer handle: {buf_id}"));
                Ok(Value::Array(Arc::new(vec![])))
            }
        }
        "rt_winit_buffer_free" => {
            // rt_winit_buffer_free(buffer_id)
            let buf_id = get_i64(args, 0, name)?;
            PIXEL_BUFFERS.lock().remove(&buf_id);
            Ok(bool_value(true))
        }
        "rt_winit_save_pixels_bmp" => {
            let path = get_string(args, 0, name)?;
            let width = get_i64(args, 1, name)?.max(1) as u32;
            let height = get_i64(args, 2, name)?.max(1) as u32;
            let pixels = get_pixels(args, 3, name)?;

            let row_size = ((width * 3 + 3) / 4) * 4; // BMP rows padded to 4-byte boundary
            let pixel_data_size = row_size * height;
            let file_size = 54 + pixel_data_size;

            let mut data = Vec::with_capacity(file_size as usize);

            // BMP file header (14 bytes)
            data.extend_from_slice(b"BM");
            data.extend_from_slice(&file_size.to_le_bytes());
            data.extend_from_slice(&[0u8; 4]); // reserved
            data.extend_from_slice(&54u32.to_le_bytes()); // pixel data offset

            // DIB header (BITMAPINFOHEADER, 40 bytes)
            data.extend_from_slice(&40u32.to_le_bytes()); // header size
            data.extend_from_slice(&width.to_le_bytes());
            data.extend_from_slice(&height.to_le_bytes());
            data.extend_from_slice(&1u16.to_le_bytes()); // planes
            data.extend_from_slice(&24u16.to_le_bytes()); // bits per pixel
            data.extend_from_slice(&0u32.to_le_bytes()); // compression (none)
            data.extend_from_slice(&pixel_data_size.to_le_bytes());
            data.extend_from_slice(&2835u32.to_le_bytes()); // h resolution (72 DPI)
            data.extend_from_slice(&2835u32.to_le_bytes()); // v resolution
            data.extend_from_slice(&0u32.to_le_bytes()); // colors in palette
            data.extend_from_slice(&0u32.to_le_bytes()); // important colors

            // Pixel data (bottom-up, BGR)
            let pad_bytes = (row_size - width * 3) as usize;
            for y in (0..height).rev() {
                for x in 0..width {
                    let idx = (y * width + x) as usize;
                    let argb = if idx < pixels.len() { pixels[idx] } else { 0 };
                    let b = (argb & 0xFF) as u8;
                    let g = ((argb >> 8) & 0xFF) as u8;
                    let r = ((argb >> 16) & 0xFF) as u8;
                    data.push(b);
                    data.push(g);
                    data.push(r);
                }
                for _ in 0..pad_bytes {
                    data.push(0);
                }
            }

            match std::fs::write(&path, &data) {
                Ok(()) => Ok(bool_value(true)),
                Err(err) => {
                    set_last_error(format!("failed to write BMP: {err}"));
                    Ok(bool_value(false))
                }
            }
        }
        _ => unreachable!("dispatch_buffer called with unexpected name: {name}"),
    }
}

fn draw_text_into_buffer(buf: &mut PixelBuffer, x: i64, y: i64, text: &str, fg: u32, bg: u32) {
    let sw = buf.width as i64;
    let sh = buf.height as i64;
    let stride = sw as usize;
    let mut cx = x;

    for ch in text.chars() {
        if cx < sw && cx + 8 > 0 && y < sh && y + 16 > 0 {
            let glyph = glyph_8x16(ch as i32);
            for (row, bits) in glyph.iter().enumerate() {
                let py = y + row as i64;
                if py < 0 || py >= sh {
                    continue;
                }
                for col in 0..8 {
                    let px = cx + col;
                    if px < 0 || px >= sw {
                        continue;
                    }
                    let mask = 0x80u8 >> col;
                    let color = if (bits & mask) != 0 { fg } else { bg };
                    buf.pixels[(py as usize) * stride + (px as usize)] = color;
                }
            }
        }
        cx = cx.saturating_add(8);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn draw_text_extern_writes_glyph_pixels() {
        let id = match dispatch_buffer(
            "rt_winit_buffer_create",
            &[Value::Int(24), Value::Int(16), Value::Int(0)],
        )
        .unwrap()
        {
            Value::Int(id) => id,
            other => panic!("expected buffer id, got {other:?}"),
        };

        let ok = dispatch_buffer(
            "rt_winit_buffer_draw_text",
            &[
                Value::Int(id),
                Value::Int(0),
                Value::Int(0),
                Value::Str("A".to_string()),
                Value::Int(0xFFFFFFFFu32 as i64),
                Value::Int(0xFF000000u32 as i64),
            ],
        )
        .unwrap();
        assert_eq!(ok, Value::Bool(true));

        {
            let bufs = PIXEL_BUFFERS.lock();
            let buf = bufs.get(&id).expect("buffer should exist");
            assert!(buf.pixels.iter().any(|&p| p == 0xFFFFFFFF));
            assert!(buf.pixels.iter().any(|&p| p == 0xFF000000));
        }

        let _ = dispatch_buffer("rt_winit_buffer_free", &[Value::Int(id)]).unwrap();
    }
}
