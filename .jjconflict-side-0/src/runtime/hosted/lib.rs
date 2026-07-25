//! Simple Hosted-Surface Runtime Bindings (Row 3 — Phase C)
//!
//! This crate exposes the `rt_cocoa_*` / `rt_win32_*` /
//! `rt_hosted_select_surface` / `rt_webgpu_*` SFFI symbols consumed by
//!   - `src/os/compositor/hosted_backend_cocoa.spl`
//!   - `src/os/compositor/hosted_backend_win32.spl`
//!   - `src/os/compositor/hosted_backend.spl`
//!   - `src/lib/gc_async_mut/gpu/engine2d/backend_webgpu.spl`
//!
//! The goal is:
//!   1. Symbols exist on every host so the Simple link step resolves.
//!   2. On the target host (macOS / Windows), the functions do something
//!      useful-enough for Row 3 (CGContext fill + present on Cocoa,
//!      BitBlt on Win32). Metal / Direct2D are explicitly *not* here —
//!      see `doc/03_plan/v2_hosted_engine2d_rewiring.md` §"Phase C".
//!   3. Non-target platforms return sentinel errors (`-1` for handle-returns,
//!      `false` for bool-returns) so the Simple side falls back cleanly.
//!
//! The module layout matches the Simple-side placeholder symbol families:
//!   - `cocoa`  — `rt_cocoa_window_*` / `rt_cocoa_layer_*` / `rt_cocoa_event_pump`
//!   - `win32`  — `rt_win32_window_*` / `rt_win32_dib_*` / `rt_win32_message_pump`
//!   - `select` — `rt_hosted_select_surface`
//!   - `webgpu` — `rt_webgpu_is_available` / `rt_webgpu_init` /
//!                `rt_webgpu_shutdown` / `rt_webgpu_create_surface` /
//!                `rt_webgpu_destroy_surface` / `rt_webgpu_upload_pixels` /
//!                `rt_webgpu_present`
//!
//! All extern "C" symbols live inside the submodules via `#[no_mangle]` so
//! their names are exported verbatim to the Simple linker (same pattern as
//! the rest of `src/runtime/*`).

#![allow(clippy::missing_safety_doc)]

pub mod cocoa;
pub mod js_test262;
pub mod select;
pub mod webgpu;
pub mod win32;
