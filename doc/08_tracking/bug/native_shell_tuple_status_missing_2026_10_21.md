# Native legacy shell tuple/status exports are absent

Canonical ID: `native_shell_tuple_status_missing_2026_10_21`.
Status: implementation in progress; bootstrap-focused verification pending.
Bug DB reconciliation pending qualified full CLI.

At frozen producer source `3050022d5d5`, the full bootstrap entry closure
compiled 1437 modules with zero HIR failures, then failed to link exact native
symbols `rt_shell_exec_tuple` and `rt_shell_exit_code`, referenced by
`std.nogc_sync_mut.sffi.process`. Retained original evidence:
`D:/dev/simple-http-client-imports-20261021/build/mir-json-fullscope/trace-fixed.log`.
The extern declarations already existed at `380200890ff`.

The admitted frozen native-all/backfill/hosted archives do not export these
symbols. The generated core-C supplement supplies scalar `rt_shell_exec` only;
its old implementation discards `pclose` status. Interpreter registrations are
not native ABI providers and are outside the Rust runtime ratchet extraction
root. Source repair therefore supplies real C and Rust-native counterparts.

The scalar contract retains stdout capture, inherited stdin/stderr, nil on
spawn/allocation failure, and adds initially-zero thread-local last status.
Windows close status is direct; POSIX normal exit status is decoded, and
signal/spawn failure is -1. Atomic tuple capture returns stdout/stderr/status
without changing scalar last-status. It delegates to existing real process
capture with timeout 0 (unbounded), not the lossy fallback process-run owner.

New runtime source changes invalidate runtime source fingerprints. The original
producer/native-all archives and all their objects/receipts must stay intact;
private updated core-C supplements are diagnostic only until fresh authority is
reviewed. No alias to interpreter dispatch, fake getter, generated stub, or
single-lane ratchet exception admits this repair.

Reproducer/generalization: `test/fixtures/runtime/native_shell_provider/main.spl`
checks initial/updated/reset status, separate streams, nonzero statuses, quoted
payloads, and tuple noninterference. Windows only; other host results remain
unverified. Thread isolation, native Rust counterpart, Simple twin and dual-run
checks remain pending before completion.

Provider input/output/cache-read/cache-create tokens: unavailable. Comparable
cohort average and usage ratio: unavailable, not guessed or zero-filled.
