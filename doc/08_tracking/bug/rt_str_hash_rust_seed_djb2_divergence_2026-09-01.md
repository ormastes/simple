# Rust seed's `rt_str_hash`/`rt_hash_text` is djb2, not FNV-1a — third lane divergence

- **Status:** OPEN — filed as the promised standalone follow-up from
  `doc/08_tracking/bug/rt_str_hash_truncated_fnv_offset_basis_bootstrap_lane_2026-08-31.md`,
  whose "Status" line says the divergence "stays OPEN as its own follow-up" but
  which did not itself carry a separate record. This file is that record.

## What was fixed (2026-08-31, `d6058da379c`, not this record)

The two C lanes (`src/runtime/runtime.c` and
`src/runtime/runtime_legacy_core.c`) both now use the correct FNV-1a-64 offset
basis `14695981039346656037` for `rt_str_hash`/`rt_hash_text`. Re-verified
here 2026-09-01 by building and running
`src/runtime/test/rt_core_abi_untested_selfcheck.c` end to end on
Windows/MinGW (gcc, 52 of 54 runtime TUs compiled — the 2 skips are the
documented external-SDK ones, `simple_counterpart_abi.h` and `wasmtime.h` —
linked with `--allow-multiple-definition`, stubs for the 8 SDK-only symbols):
`PASS: 23 check(s), 0 failure(s)`, including
`H0 rt_str_hash(empty) == FNV-1a-64 offset basis (got -3750763034362895579)`
and
`H1 rt_str_hash(simple) == reference FNV-1a-64 (got -5909502519632118881)`.
Both C source files were also grep-verified to carry byte-identical basis
constants and identical loop bodies
(`runtime.c:548`, `runtime_legacy_core.c:244`), so the fix applies uniformly
to whichever TU a given lane links, not just to the one bound by this
particular harness link.

## What is NOT fixed and is this record's subject

The Rust seed's runtime crate never used FNV-1a for these two symbols. It
uses djb2 (seed `5381`, multiplier `33`) and always has:

```rust
// src/compiler_rust/runtime/src/value/collections.rs:4553-4574
pub extern "C" fn rt_hash_text(string: RuntimeValue) -> i64 {
    ...
    let mut hash = 5381u64;
    unsafe {
        for byte in std::slice::from_raw_parts(data, len as usize) {
            hash = hash.wrapping_mul(33).wrapping_add(*byte as u64);
        }
    }
    hash as i64
}

#[no_mangle]
pub extern "C" fn rt_str_hash(string: RuntimeValue) -> i64 {
    rt_hash_text(string)
}
```

So there are, and remain, three independent hash *algorithms* answering the
same two symbol names depending on which lane links them: two C TUs computing
FNV-1a-64 (now in agreement with each other) and the Rust seed computing
djb2. A string hashed by the seed and read back by a C-lane binary (or vice
versa) gets a different number.

## Why this is judged benign today (not why it should stay unfixed forever)

1. **Nothing persisted crosses this boundary.** The only on-disk consumers of
   `rt_hash_text`-shaped values found in this codebase
   (`cache_validator.spl:162`, `shb_cache.spl:89`) compare a freshly computed
   hash against a `source_hash` trailer field written by the SAME process
   that later reads it back — i.e. same-lane round-trips, not cross-lane. A
   mismatch there fails closed to a full rebuild (safe direction), so a
   same-lane hasher swap is invisible; what would NOT be safe is a
   cross-lane read of a value the Rust seed wrote being validated by C-lane
   code, or vice versa. No such path was found.
2. **In-memory dict bucketing does not use these symbols at all.** Dict
   hashing goes through the static, internal `rt_core_dict_hash`
   (`src/runtime/runtime_native.c:8314`), which is a separate FNV-1a
   implementation (still carrying the truncated 19-digit basis
   `1469598103934665603` at line 8317 — also out of scope for the
   2026-08-31 fix, since it is in-memory-only and self-consistent within a
   single process). `rt_str_hash`/`rt_hash_text` are not on that path.
3. **The seed is bootstrap-only.** Per `CLAUDE.md`, tooling
   (`test`/`lint`/`fmt`/`build`/`run`/MCP/LSP) runs on the self-hosted
   `bin/release/<triple>/simple`, not the Rust seed — the seed's job is
   producing that binary, not serving as a long-lived lane whose hash values
   get compared against C-lane output.

## What would make it NOT benign (why this stays open rather than closed)

- Any future code path that computes `rt_str_hash`/`.hash()` in one lane and
  persists or transmits the result for another lane to compare (a cache key,
  an IPC frame, a content-address, a test fixture) would silently break the
  moment it crossed the seed/C-lane boundary. The 2026-08-31 fix's own
  reasoning ("no persisted cross-lane identity can exist") is a fact about
  the CURRENT call graph, not an invariant enforced anywhere — nothing stops
  a later change from adding such a path.
- `rt_core_abi_untested_selfcheck.c`'s oracle (H0/H1) pins only the C-lane
  answer; it does not build or run against the Rust seed's `rt_str_hash`, so
  a regression back to djb2 in a C lane would be caught, but the seed's djb2
  itself is not under any regression pin.

## Recommended resolution (not done here — scope decision only)

Align the Rust seed's `rt_str_hash`/`rt_hash_text` to the same FNV-1a-64
algorithm and offset basis as the C lanes (`14695981039346656037` basis,
`1099511628211` prime), matching `src/runtime/simple_core/core_string.spl`'s
`rt_str_hash`/`rt_hash_text` contract already documented for the pure-Simple
bridge (`FNV_OFFSET -3750763034362895579`). This is a real seed-crate change
with its own blast radius (any seed-only code path that already depends on
djb2's specific bucket distribution or numeric output) and needs its own
review; it is being filed rather than made here to avoid conflating it with
the narrower, already-landed C-lane fix.

## Unix impact

Pure algorithmic — no platform conditionals in either the current djb2 code
or the proposed FNV-1a-64 replacement. Whatever is decided applies
identically on Linux/macOS/Windows; the seed crate has no per-OS branch on
this function.
