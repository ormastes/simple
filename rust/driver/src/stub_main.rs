//! Minimal settlement stub executable.
//!
//! When built, this binary can have settlement data appended to it.
//! At runtime, it calls rt_settlement_main() to find and execute
//! the appended settlement data.

fn main() {
    // Link to the runtime's settlement_main function
    let exit_code = simple_runtime::loader::startup::settlement_main();
    std::process::exit(exit_code);
}
