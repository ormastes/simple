// Simple Language UI — Tauri v2 Shell (desktop entry point)
//
// Delegates to the shared run() in lib.rs, which handles both desktop and
// mobile entry points.

#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")]

fn main() {
    simple_tauri_shell_lib::run();
}
