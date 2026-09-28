# Target 6 pinned archive packed file-view evidence (2026-09-29)

Status: focused Linux Stage-2 native improvement; Target 6 production
qualification and current-source Stage-4 bootstrap remain open.

## Cause and change

The POSIX file-view owner converted every descriptor byte into a tagged
`i64` array slot. On an 8 MiB archive, the bounded 64 KiB reader trial made
256 additional anonymous `mmap` calls of 528,384 bytes each: two large
allocations per read. The earlier whole-file reader avoided repeated calls
but retained an eightfold byte-array representation.

`runtime_file_view.c` now returns the runtime's packed `[u8]` array via
`rt_byte_array_new_len` and `rt_array_set`. Its descriptor identity, no-follow
path, read range, short-read, and close behavior are unchanged. The C
file-view selfcheck passes. A copied host runtime capsule with only the
`runtime_file_view.o` member replaced linked a no-stub native benchmark and
the pinned archive integration spec; the original capsule was untouched.

## Paired 8 MiB result

The same deterministic 8,388,608-byte CAS file was opened and digest checked
by binaries built from the same Simple sources and Stage-2 compiler. One
binary used the prior runtime object; one used the packed-array object.
Both were warmed once, then run in nine alternating pairs on the same host
under a 2 GiB virtual-memory limit. Every run returned `pass`.

| Measure | Prior runtime | Packed runtime | Packed / prior |
| --- | ---: | ---: | ---: |
| p95 elapsed | 0.56 s | 0.41 s | 0.732 |
| Median elapsed | 0.52 s | 0.40 s | 0.769 |
| Peak RSS | 76,760 KiB | 19,512 KiB | 0.254 |

The normalized p95 time plus peak RSS ratio is **0.986**, below the `<2`
gate and beyond sample noise. The baseline elapsed range was 0.51–0.56 s;
the packed range was 0.39–0.41 s. Both benchmark binaries were 118,024
bytes. Full samples and fixture identity are in
`target6_pinned_digest_packed_8m_pair_2026-09-29.json`.

The no-stub native pinned archive spec also passed 9/9 scenarios against the
packed runtime, including the 542-byte and 131 KiB persisted archives
(0.16 s, 11,356 KiB peak RSS). This covers this file-view boundary on Linux.
It does not establish full compile/check/bootstrap/MCP/LSP cutover, cross-OS
parity, larger maximum-archive hard budgets, or a current-source Stage-4
bootstrap. Those remain release gates.
