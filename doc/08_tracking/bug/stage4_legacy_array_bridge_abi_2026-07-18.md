# Stage4 legacy bridges returned incompatible arrays

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

## Symptom

`runtime_native` used legacy `spl_array_*` constructors in `rt_bytes_from_raw`
and delegated `rt_strsplit` to `spl_str_split`. Those helpers build the legacy
`SplValue` array layout, while pure-Simple Stage4 callers consume canonical
tagged `RtCoreArray` values. `rt_bytes_from_raw` is reachable from LLVM object
emission, so archive section projection cannot make the mismatch safe.

## Fix and prevention

Both bridges now construct canonical arrays through the existing
`rt_byte_array_new_len`, `rt_array_new`, `rt_array_push`, and `rt_string_new`
owners. The focused runtime C test covers byte values `0`, `127`, and `255`, a
null source, empty split fields, no-match splitting, and an empty delimiter.

Raw `runtime_legacy_core.o` remains forbidden as a Stage4 candidate: it still
exports no-op dictionary operations and other bridge-only legacy layouts. A
future compatibility capsule must expose only audited raw-string/platform
helpers and reject legacy array, dictionary, and split exports.

No Simple, compiler, runtime, C, Rust, Cargo, or native execution is claimed in
this static-only session.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro in the record, no status line existed); closed as stale per the "too old / not valid -> close" triage policy. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
