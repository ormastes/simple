# Mode-aware text operations coverage and memory — 2026-08-26

The direct production-owner suite passes 5/5 and measures
`src/lib/common/encoding/text_ops.spl` at 100% branches (70/70) and 98% lines
(172/174). It covers byte and scalar compatibility modes, bounds, slicing,
iteration, every simplified width/script range, fallthrough, and indexed
delegation.

Four malformed-sequence fallbacks were removed from traversal. Safe `text` is
validated UTF-8, so truncated sequences and zero decode progress are impossible
inside this owner; malformed-byte handling belongs at construction/decoding.

The focused performance smoke passes 1/1 over seven samples and 1,792 mixed
ASCII/multilingual iterations. It reports p50/p95 397,577/413,919 us,
whole-process HWM 51,564 KiB, and checksum 232,960. Execution fell back to the
interpreter, so timing is not a native baseline. Allocation, allocated, and
retained bytes remain unavailable; checkpoint bytes are structurally zero for
this non-index-building workload.
