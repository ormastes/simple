// Local stub for the temporary bug-C8 vtable debug hook referenced by
// driver/src/main.rs. The real investigation module is a peer's uncommitted
// file that a working-copy sweep removed; this no-op stub restores buildability
// so the seed can rebuild. Only reached under SIMPLE_DEBUG_VTABLE_TEST.
pub fn run() {}
