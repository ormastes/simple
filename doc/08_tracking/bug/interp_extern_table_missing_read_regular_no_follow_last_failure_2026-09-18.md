# Seed interpreter extern table missing rt_file_read_regular_no_follow_last_failure (semantic abort)

Date: 2026-09-18
Lane: release v1.0.0-beta line (kimi-20260915-beta2)
Severity: release-blocking (any interpreted native-build worker)
Status: fixed in v1.0.0-beta.11

## Symptom

Release `v1.0.0-beta.10` windows-x86_64 leg, ~6 s into the worker compile:

```
error: semantic: unknown extern function: rt_file_read_regular_no_follow_last_failure
```

## Cause

`src/lib/nogc_sync_mut/io/file_ops.spl:39` declares
`extern fn rt_file_read_regular_no_follow_last_failure() -> i64` (the diagnostic
companion that explains which of the bounded no-follow reader's eight NIL arms
fired). The seed's semantic pass validates extern declarations against the
interpreter extern table (`compiler/src/interpreter_extern/mod.rs`). That table
registered `rt_file_read_regular_no_follow_bounded` but never its companion —
same gap class as the documented `rt_string_ends_with` /
`rt_string_rfind` episodes (see comments at mod.rs around the string entries).

Why only now: the companion declaration is recent (added with the READ_NF arm
diagnostics), and every earlier worker died before the semantic pass reached
`nogc_sync_mut/io/file_ops.spl` — beta.7 at inventory publication, beta.8 at
the parser `namespace` abort, beta.9 at the shard-leak OOM. beta.10's worker
was the first to survive that far. This wall was platform-independent; the
linux-x86_64 leg has been externally cancelled before reaching native-build in
every beta, so windows reported it first.

## Fix

- `compiler/src/interpreter_extern/file_io.rs`: thread-local arm recorder for
  the interpreter twin of the bounded reader (mirrors the runtime crate's
  READ_NF_* codes: 77 never-called, 100 ok, 2..=10 named arms), recorded on
  every NIL return and on success; new
  `rt_file_read_regular_no_follow_last_failure` returns the arm.
- `compiler/src/interpreter_extern/mod.rs`: `insert_simple!` registration for
  the companion next to the bounded reader.

`cargo check -p simple-compiler` clean. Runtime/AOT tables already had the
symbol (runtime_sffi.rs, value/mod.rs); the 0-arg signature needs no codegen
arg-tag entries.

## Audit note

A repo-wide diff of `extern fn rt_*` declarations in src/ vs every quoted
`rt_*` name in the seed shows ~600 more unregistered names, but nearly all are
in optional domains the bootstrap_main closure never compiles (ssh/ftp/torch/
vulkan/metal/gamepad/lyon/zip/dap/dwarf/ptrace...). The release run itself is
the closure test; each remaining gap of this class costs one CI cycle to
surface. Consider a startup-time closure extern audit as a follow-up.
