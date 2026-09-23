# Checked integer-array bridge: missing Rust lane

Resolved publication blocker at base `6d33ed254d4`.

The C GPU adapter introduced `rt_array_i64_validate` and
`rt_array_i64_copy_checked` without Rust definitions. The dual-runtime gate also
found 13 obsolete `rust-only` baseline rows for already implemented C CUDA,
Vulkan, and thread-local adapters. Exactly those rows were removed after checking
both source lanes; the baseline was not regenerated.

The Rust bridge preserves the C ABI and contract: return the length or `-22`,
accept boxed-element arrays of inline signed integers, reject packed byte/u64
arrays, tuples, invalid handles, and noninteger elements, and validate the whole
source before writing any destination element. It also checks lengths against
capacity and Rust slice limits. Empty arrays accept a null destination with
nonnegative capacity. Both calls require a live source without concurrent
mutation/free; the copy requires valid disjoint caller-owned output storage.
These helpers are O(n), use O(1) extra space, and allocate no temporary buffers.
Full-width heap-boxed integers remain outside this existing C bridge contract.

Focused verification on macOS arm64:

- Private qualified `nightly-2026-09-16` toolchain, absolute `cargo`, `RUSTC`,
  and `RUSTDOC`; isolated target directory
  `build/evidence/rt-i64-dual-20260923/target`.
- `cargo test -p simple-runtime --lib --no-default-features array_i64::tests
  --offline --jobs 2`: four tests passed, 1,256 unrelated tests filtered out.
  Build took 56 seconds; no bootstrap or compiler build was run.
- `sh scripts/check/check-array-i64-checked-c.shs`: C counterpart passed signed
  boundaries, capacity/null errors, no partial write, empty arrays, invalid and
  freed handles, and rejected packed representations.
- `check-rt-dual-implementation-ratchet.shs --root <P0>`: seven selftests passed;
  2,495 symbols matched 2,495 baseline rows, zero new and zero stale.
- Independent Astra review passed the Rust implementation, ABI, memory bounds,
  and all 13 baseline deletions. Its C fixture review required keeping assertions
  enabled even when callers supply `CFLAGS=-DNDEBUG`; the wrapper now appends
  `-UNDEBUG` after caller flags. That configuration passed the C contract;
  the final independent review accepted the assertion and sentinel fixes.

The census proves counterpart existence, not universal GPU provider semantic
parity. No GPU hardware, full bootstrap, or release qualification is claimed.
