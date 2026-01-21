//! Minimal executable stub for Simple settlement executables.
//!
//! This stub is compiled once and embedded in settlement executables.
//! When run, it loads the settlement data appended to itself and executes it.

fn main() {
    std::process::exit(simple_loader::settlement_main());
}
