//! Fail-closed Rust twins of the C-only `rt_gui_*` HTML GUI provider and
//! event-session API (`src/runtime/runtime_native.c`, the block starting at
//! `rt_gui_html_ready`). The C lane dlopens the provider named by
//! `SIMPLE_GUI_HTML_PROVIDER_PATH` on macOS/Linux and runs event sessions on
//! the macOS main thread only. This crate has no GUI provider dynload path,
//! so every twin takes exactly the branch the C lane takes on a host where the
//! feature is unsupported -- the `_WIN32` branch of `rt_gui_html_load` for the
//! standalone HTML call, and the non-`__APPLE__` branch of
//! `rt_gui_event_owner` for the four session calls -- unconditionally, on
//! every OS. These are dual-implementation-ratchet twins, not a port of the
//! dlopen/dlsym provider machinery: the refuse messages, the exit status
//! (70) and the order in which each check fires are the C lane's, verbatim.
//!
//! State the C lane keeps to police reentry and standalone/session overlap
//! (`rt_gui_event_in_callback`, `rt_gui_call_gate`, `rt_gui_event_active`,
//! `rt_gui_event_ready`) is deliberately absent: no provider callback and no
//! session can ever be admitted on this lane, so none of those checks can
//! ever fire ahead of the unsupported-host refusal that precedes them in C.

use crate::value::{HeapObjectType, RuntimeValue};

/// Contract: `static void rt_gui_html_refuse(const char *reason)`
/// (`runtime_native.c`). Prints the C lane's exact diagnostic line to stderr
/// and exits with status 70. C-`static`, so not exported here either.
fn rt_gui_html_refuse(reason: &str) -> ! {
    eprintln!("[simple-gui] HTML provider unavailable: {reason}");
    std::process::exit(70);
}

/// Contract: `static void rt_gui_html_load(void)`. On a host without the
/// dlopen provider path (C's `_WIN32` branch) the C lane refuses before
/// touching any provider state; this crate has no provider path on any host,
/// so it always takes that branch.
fn rt_gui_html_load() -> ! {
    rt_gui_html_refuse("dynamic HTML provider unsupported on this host");
}

/// Stand-in for the C lane's `static int64_t (*rt_gui_html_present)(const
/// uint8_t *, uint64_t)` provider entry slot, which stays `NULL` until
/// `rt_gui_html_load` succeeds. C refuses "provider rejected frame" when
/// the slot is `NULL` at the call site in `rt_gui_present_html`. Unreachable
/// on this lane because `rt_gui_html_load` never returns; kept so the twin
/// population matches the C lane symbol for symbol.
#[allow(dead_code)]
fn rt_gui_html_present(_html: *const u8, _len: u64) -> i64 {
    rt_gui_html_refuse("provider rejected frame");
}

/// Contract: `static void rt_gui_event_owner(void)`. C's non-`__APPLE__`
/// branch refuses every session call outright; the main-thread and
/// callback-reentry checks that follow it are macOS-only.
fn rt_gui_event_owner() -> ! {
    rt_gui_html_refuse("GUI event sessions require macOS");
}

/// Contract: `void rt_gui_present_html(int64_t tagged_html)`
/// (`runtime.h:900`). C order: callback-reentry check (never set here),
/// tagged-text decode ("invalid tagged text"), standalone/session gate
/// (always open here), then `rt_gui_html_load`, which refuses on an
/// unsupported host. Only the decode and the load refusal are observable
/// on this lane, in that order.
#[no_mangle]
pub extern "C" fn rt_gui_present_html(tagged_html: RuntimeValue) {
    if tagged_html.heap_type() != Some(HeapObjectType::String) {
        rt_gui_html_refuse("invalid tagged text");
    }
    rt_gui_html_load();
}

/// Contract: `void rt_gui_begin_session(void)` (`runtime.h:901`). C calls
/// `rt_gui_event_owner` first, which refuses off macOS.
#[no_mangle]
pub extern "C" fn rt_gui_begin_session() {
    rt_gui_event_owner();
}

/// Contract: `void rt_gui_session_present_html(int64_t tagged_html)`
/// (`runtime.h:902`). C calls `rt_gui_event_owner` before decoding the
/// argument, so off macOS the argument is never inspected.
#[no_mangle]
pub extern "C" fn rt_gui_session_present_html(_tagged_html: RuntimeValue) {
    rt_gui_event_owner();
}

/// Contract: `int64_t rt_gui_poll_event(void)` (`runtime.h:903`). C calls
/// `rt_gui_event_owner` first, which refuses off macOS; no event text is
/// ever allocated or returned on this lane.
#[no_mangle]
pub extern "C" fn rt_gui_poll_event() -> i64 {
    rt_gui_event_owner();
}

/// Contract: `void rt_gui_end_session(void)` (`runtime.h:904`). C calls
/// `rt_gui_event_owner` first, which refuses off macOS.
#[no_mangle]
pub extern "C" fn rt_gui_end_session() {
    rt_gui_event_owner();
}
