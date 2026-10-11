# Phase 1 mapped-byte read source contract ownership

Release `63e81107bfdca403dfbfa4269169e10fcd9dfd90` reproduces the retained
`native_mmap_byte_read_spec.spl` result: three real raw-pointer/binary behavior
cases pass; the fourth source contract fails. The nested loader module is a
delegating adapter, but the contract expects the `rt_bytes_from_raw` body there.
The actual bulk-copy body resides in `compiler.loader.smf_mmap_native`.

The repaired contract asserts the adapter's alias and delegation, the physical
owner's bulk call, and the original forbidden reserve/pointer-cast checks in
both files. No original assertion is removed; the three behavioral cases are
unchanged. No production file changes.

## Evidence and limits

`build/phase1-mmap-read-owner-contract-20261011` contains the retained command,
current baseline, final case projection, and logs. The projection copies the
exact final affected case body, with its unchanged imports, into an isolated
executable specification. This prevents replaying the three passing cases.

| Check | Result |
| --- | --- |
| Current release baseline | 3/4, exit 1, 1.44 seconds |
| Exact final affected source-contract case | 1/1, exit 0, 0.57 seconds |
| Producer SHA256 | `15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb` |

These are incremental **BOOTSTRAP_ONLY_DIAGNOSTIC** results, not a repeated
full-file 4/4 run or production/native admission. No compiler rebuild or
previously green check replay occurred. Test-only scope does not alter runtime
startup, native mapping, platform performance, or packaging.

Separately, cleanup recovery remains unresolved: release baseline 5/6 and an
isolated construction-failure trace return `native-outcome-empty`, before any
release dispatch. Evidence is retained in
`build/phase1-cleanup-recovery-20261011/classification.json`. No cleanup identity
authentication was weakened and no fabricated dispatch was introduced.

The global 4,758-row candidate queue is unchanged. Existing production loader
drafts retain admitted-runtime qualification gates.
