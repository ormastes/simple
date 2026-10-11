# Full CLI Phase2 construction lacks selected core ABI symbols

Status: OPEN.

A separate user-authorized full CLI bootstrap construction from release source `d66172f8fde` plus the folded-scalar helper fix compiled 2,570 modules without compilation failures, then failed linking against the pinned `core-c-bootstrap` runtime. The linker reported 157 distinct undefined symbols, including optional GPU/font/SDL/SQLite interfaces and `min_i64`. Runtime and Rust source were unchanged between the pinned runtime-owner branch base and the selected release commit.

Evidence: `build/native_probe/traceability-release-cli-pass1/construction.log` and retained native objects. There is no full CLI artifact or general interpreter qualification. Do not stub the symbols, switch to retired runtime bundles, or report compilation-only success as execution qualification. Separate narrow products remain independently runnable.
