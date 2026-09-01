# WidthIndex coverage and memory — 2026-08-26

The direct wrapper suite passes 5/5 and measures
`src/lib/common/encoding/width_index.spl` at 100% branches (25/25) and 96% lines
(78/81). It covers 1/2/3/4-byte scalar coordinates, negative and terminal
bounds, slicing, cached scalar length, lazy threshold, small-text suppression,
SWI dispatch, both SWI-to-rank/select fallbacks, and linear/SWI/rank cleanup.

Branches for failed native handle creation, truncated scalars, out-of-buffer
copy, and negative `[u8]` values were removed because they contradict the
validated-text, typed-byte, and registry-handle contracts. Resource exhaustion
must be reported by a typed fallible builder rather than a silent zero handle.

The performance smoke passes 1/1. Seven 4,096-scalar index build/query/free
samples executed 7,168 coordinate queries over 10,240 input bytes, with checksum
20,177,563. Interpreter p50/p95 was 14,589/16,481 us and process HWM 47,500 KiB.
Allocation, index-storage, and post-free retained bytes are unavailable, so this
is not a native or memory-qualified receipt. It also does not cover the Rust
global full-offset registry's internal branches or prove reclamation.
