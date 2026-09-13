## Closed 2026-09-13 — prior in-body resolution, carried forward (NOT re-verified this pass)

Reviewed in the 2026-05-and-earlier bug/todo tracking sweep. This entry already
recorded its own resolution before this pass; the header exists so the closure is
visible at the top rather than buried in the body. First status line found:

> Status: Fixed (2026-05-19)

This is a closure marker, not a new claim: the repro was **not** re-run in this
sweep. The original evidence in the body stands on its own. Re-open with a fresh
dated repro if the symptom returns — do not treat this header as verification.

---

# File Write Truncates Generated Compression Byte Buffers

Date: 2026-05-13
Status: Fixed (2026-05-19)

Host-tool compatibility checks for generated zstd/xz buffers exposed a file-write seam: `rt_file_write_bytes(path, encoded)` wrote only a truncated payload for buffers returned by the pure compression encoders. One observed zstd frame file contained a single byte (`0x0c`), causing host `zstd` to report `unknown header` even though in-process decode of the same generated buffer succeeded.

Current handling: compression framework and zstd frame specs assert in-process encode/decode compatibility for these generated buffers. Host decode coverage remains available for host-generated input fixtures that are read with `rt_file_read_bytes`.

Root cause: `rt_file_write_bytes` in `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs` used `filter_map` that only matched `Value::Int(i)` and silently dropped all other variants via `_ => None`. Compression encoders (e.g. `_zstd_write_le32`, `_zstd_append`) build `[u8]` arrays using `as u8` casts, which produce `Value::UInt { value, width: 8 }` elements — not `Value::Int`. Every such element was dropped, leaving only any incidental plain-integer elements and producing a near-empty file.

Fix: changed `filter_map` to `map` with explicit handling for both `Value::Int(i)` and `Value::UInt { value, .. }` (plus a zero fallback for unexpected tags), matching the pattern used in `rt_smf_parse_relocs` and `rt_bytes_from_raw`. Also added `FrozenArray` arm to the array-extraction match for completeness.

Fix location: `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs`, function `rt_file_write_bytes` (line ~625).
