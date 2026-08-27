# Codepoint-to-text runtime-builder candidate — 2026-08-26

The candidate replaced `text_from_codepoints`' retained `[text]` parts array
with the existing amortized `RtStringBuilder`. Correctness passed:

- UTF-8 owner: 58/58; 97% branches (39/40);
- generic codec: 30/30.

The benchmark campaign did not qualify performance. Cycle 1 exposed an invalid
fallback pattern in the new spec; cycle 2 exposed the unavailable timing extern
and was repaired to use the standard time facade; cycle 3 failed because
`rt_process_hwm_kib` is unregistered in the interpreter. At that point the
mandatory three-cycle cap ended the campaign. The shared host was additionally
contaminated by a roughly 6.3-GiB `git pack-objects`, a multi-GiB unit-test run,
and concurrent compiler jobs, so external RSS/timing would not be admissible.

The candidate and temporary benchmark were reverted. No speed, allocation, or
RSS improvement is claimed. Resume only after the process/allocator counters
are observable and the host is controlled; retain one same-corpus receipt for
reference and builder latency, allocation count/bytes, peak/steady RSS, output
bytes, and the eliminated retained-parts count.

The interpreter dispatch repair needed for that resume is now implemented in
the working tree, including real-allocation tests, but its focused Cargo test is
blocked by unrelated inconsistent compiler edits and therefore is not retained
as passing evidence.
