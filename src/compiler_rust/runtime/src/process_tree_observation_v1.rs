//! Rust host binding for the C-owned, non-reaping child observation.
//!
//! The runtime build already links runtime_process_tree.c. Keep that function
//! as the sole C ABI export; this ordinary Rust-mangled wrapper supplies the
//! Rust call surface without duplicating waitid policy or exporting a second
//! symbol with the same C name.

unsafe extern "C" {
    #[link_name = "rt_process_owned_child_state"]
    fn owned_child_state_host(pid: i64) -> i64;
}

/// 1 = owned running child, 0 = owned unreaped exit, negative = unavailable.
/// In particular, a live nonchild and a reaped child return negative ECHILD.
/// This observation does not reap, signal, or authorize session retirement.
pub fn rt_process_owned_child_state(pid: i64) -> i64 {
    unsafe { owned_child_state_host(pid) }
}
