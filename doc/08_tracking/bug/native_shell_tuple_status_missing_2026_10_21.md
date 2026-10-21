# Native legacy shell tuple/status exports are absent

Canonical ID: `native_shell_tuple_status_missing_2026_10_21`.
Status: scoped provider repair verified; full-bootstrap qualification pending.
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
unverified. The Simple reference explicitly covers tuple composition and TLS
state transitions; it does not claim to replace the scalar process boundary.
The annotated SSpec remains authored, not executed by a bootstrap-only producer.

Provider input/output/cache-read/cache-create tokens: unavailable. Comparable
cohort average and usage ratio: unavailable, not guessed or zero-filled.

## Actual focused evidence

Producer SHA256:
`32014b3401e3cb76aec44acb475a22f2385fefcd1d19ab71049e52d633356825`.
Canonical Windows MSVC environment setup and LLVM 23.1.1/clang-cl were used.
Every writable native/Cargo cache and output stayed under the private worktree
`D:/dev/simple-phase3-native-shell-20261021/build/native-shell/`.

- Real C-provider fixture: native-build linked a 279 KB executable, exited zero,
  and printed `PASS native shell provider: 14 checks including two-thread isolation`.
  Scalar stderr was retained separately as `scalar-error`; tuple stderr was
  checked independently. Initial status, failing/succeeding subprocesses,
  quoted command, and tuple noninterference passed. A tiny Windows helper tests
  native C TLS across two threads and the parent; immutable inputs/handles
  cross the boundary, and the parent joins before reading thread result codes.
  Its final form uses NIL failure on one worker and initial zero on the other,
  avoiding concurrent runtime-heap operations.
- Real native Rust runtime integration: `cargo test -p simple-runtime
  --no-default-features --features hosted-webgpu-provider --target
  x86_64-pc-windows-msvc --test native_shell_provider` passed 2/2, including
  subprocess/status/stream/quoting controls and independent thread statuses 4/9.
  The original native Rust quoted-command test failed with backslash-escaped
  quotes; repaired `/S` raw payload then passed. Retained `rust.log`.
- Standalone Rust native archive snapshot `standalone-simple-runtime.lib`, SHA
  `7ad17616cd650a787dd40813d370e335280f7cd7839b98cac5ee6914507257f8`, defines
  exactly one of each of the three shell ABI symbols (`llvm-nm --defined-only
  --extern-only`).
- Real aggregate-feature runtime build (including cdylib) passed with
  `--features hosted-webgpu-provider,native-all-provider`. Its archive snapshot
  `native-all-simple-runtime.lib`, SHA
  `9386bd943fbab3bb9841a678ac468c51643b4e19cfc670af22f94fb4fb854283`, defines
  zero of those names. The symbol-retention table is feature-aware too.
- The private updated core-C archive defines exactly one of each name. Frozen
  canonical native-all/backfill archives were never overwritten.

The tiny fixture renamed `bootstrap_main.spl` forces frozen native-all plus
updated core-C supplement. That combined link is BLOCKED on an unrelated COFF
error: `relocation against symbol in discarded section:
rt_vulkan_async_session_supported`, referenced by frozen native-all CGU.03.
Shell names resolved. Retained `tiny/bootstrap_main-build.log`; no execution or
aggregate-bootstrap PASS is claimed, and no Vulkan/retention waiver was added.

Source pairing removes only obsolete `rt_shell_exec c-only` after genuine native
Rust execution/export proof. No new single-lane exception or fake Rust helper
was introduced. Private helper names do not use the runtime ABI prefix.
