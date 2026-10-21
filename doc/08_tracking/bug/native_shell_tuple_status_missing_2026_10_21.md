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

## Earlier focused evidence (superseded aggregate ownership)

The C-only and standalone Rust executions below remain valid evidence for
their respective providers. The earlier aggregate Rust-export suppression and
zero-export archive are historical diagnostics, not the final ownership matrix.

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

The earlier tiny fixture renamed `bootstrap_main.spl` forces frozen native-all
plus updated core-C supplement. That combined link was blocked on a COFF
error: `relocation against symbol in discarded section:
rt_vulkan_async_session_supported`, referenced by frozen native-all CGU.03.
Shell names resolved. Retained `tiny/bootstrap_main-build.log`; no execution or
aggregate-bootstrap PASS is claimed, and no Vulkan/retention waiver was added.

After the separate real weak GPU-owner repair, that old mixed fixture linked
but exited 2 at scalar stdout. Its inputs came from Rust string constructors;
the strong C shell decoder requires its own string registry. This was a real
mixed-owner defect, not evidence that a fresh archive with the same suppressed
Rust exports would work. The failed logs remain at
`D:/dev/simple-windows-http-provider-20261021/build/session/gpu-owner-repair/tiny/`.

The final design restores genuine Rust shell exports and retention references
in every feature configuration. C provides real weak fallbacks (MSVC private
`core_c_shell_*` definitions with `/alternatename`, GNU weak definitions).
Aggregate callers therefore use Rust strings, tuples, capture and TLS together;
C-only executables use the complete C provider. No public-value bridge or
single-lane exception substitutes for coherent ownership.

Source pairing removes only obsolete `rt_shell_exec c-only` after genuine native
Rust execution/export proof. No new single-lane exception or fake Rust helper
was introduced. Private helper names do not use the runtime ABI prefix.

At source commit `1e4e1f9bdab`, the final C fixture including the heap-free NIL
thread case and private-helper rename built and ran successfully. Exact logs:
`tiny/main-build.log`, `tiny/main-run.stdout`, `tiny/main-run.stderr`; native
object directory `tiny/native-objects-reW8dB`. No unchanged Rust controls were
repeated after their earlier passing implementation.

Committed local-tier command
`sh scripts/check/check-rt-dual-implementation-ratchet.shs --rev HEAD
--baseline-rev 3050022d5d5` passed: 10 detector selftests, 2623 single-lane names
versus 2624 at base, zero new. Frozen-baseline drift (216 new/79 stale) was
reported by that existing differential gate as informational, not waived by a
new baseline. Retained `ratchet.log`. Scoped diff whitespace check passed.

The additional SFFI source-only queue did NOT pass:
`scripts/audit/sffi-unsafe-backlog.shs` exited 1 because its inventory dependency
reported `source_variants=407/399 migration=3613/3546`. Retained
`sffi-source-audit.log`. This global source-inventory failure is not runtime
execution evidence and is not relabeled PASS or attributed without a baseline
comparison. Full production/SPipe verification remains unclaimed.

## Final coherent ownership evidence

At implementation commit `d66c4bdf171`, both Windows native fixture paths
passed all 14 checks, including native TLS isolation, subprocess success and
failure, quoted commands, separate tuple streams, and tuple status-slot
noninterference. Scalar stderr remained inherited (`scalar-error` in each
separate run stderr log).

- C weak fallback: `tiny/final-weak-c-build.log`,
  `tiny/final-weak-c-run.stdout`, `tiny/final-weak-c-run.stderr`; exit 0,
  279 KB executable, objects `tiny/native-objects-jrDcQ5`.
- Genuine new Rust native-all plus updated C supplement:
  `tiny/final-mixed-build.log`, `tiny/final-mixed-run.stdout`,
  `tiny/final-mixed-run.stderr`; exit 0, 8425 KB executable, objects
  `tiny/native-objects-ToDx93`.
- Aggregate-feature Rust integration tests actually executed and passed 2/2:
  `final-aggregate-rust-tests.log`. Command: `cargo test --manifest-path
  src/compiler_rust/Cargo.toml -p simple-runtime --no-default-features
  --features hosted-webgpu-provider,native-all-provider --target
  x86_64-pc-windows-msvc --test native_shell_provider -- --nocapture`.
- `final-native-all-shell-symbols.txt` records one strong definition each of
  `rt_shell_exec`, `rt_shell_exec_tuple`, `rt_shell_exit_code` in the new
  aggregate. `final-c-shell-symbols.txt` and `final-c-shell-directives.txt`
  record only the three private `core_c_shell_*` definitions and their real
  MSVC weak `/alternatename` fallbacks in the C supplement.

All paths above are relative to the private `build/native-shell/` directory.
The exact finite diagnostic scripts are `default-ownership.sh`, `native.sh`
and `final-mixed.sh`. Both native rows use the frozen producer hash recorded
above, `--backend llvm --runtime-bundle core-c-bootstrap --source src
--entry-closure --threads 1 --mode one-binary --target
x86_64-pc-windows-msvc`, with distinct output and cache paths. The mixed row
uses `src/bootstrap_main.spl` to select the aggregate route.

The new archive was built with `cargo build --manifest-path
src/compiler_rust/Cargo.toml -p simple-native-all --target
x86_64-pc-windows-msvc --lib`, with private `CARGO_TARGET_DIR` and two jobs.
Its SHA256 is
`be4a24cb99c0793aa33397f74336d0996490b11e5828eeb94912ff703997d16a`.
This default-feature choice follows
`scripts/bootstrap/build-coherent-frozen-provider.shs`: LLVM Support embedding
is excluded from that coherent provider route. An earlier explicit optional
`--features llvm` invocation failed in `aya-llvm-sys` because the installed
Windows `llvm-config` rejected dynamic linking; its unchanged failure is
retained in `new-native-all-build.log`, not relabeled as a runtime failure.

`final-mixed-runtime/diagnostic-components.txt` records the distinct new
aggregate and unchanged frozen backfill/LLVM/hosted components. No frozen
archive, producer, receipt, or cache was overwritten or rebound. This private
mixed fixture proves the repaired ownership boundary; fresh canonical
authority and full-bootstrap qualification remain the campaign owner's work.

The actual final implementation ratchet passed once at `d66c4bdf171` with
`sh scripts/check/check-rt-dual-implementation-ratchet.shs --rev HEAD
--baseline-rev 3050022d5d5`: 10 selftests, 2623 versus 2624 single-lane
symbols, zero new; retained `final-ratchet.log`. Only the obsolete scalar
`rt_shell_exec c-only` baseline entry was removed after genuine Rust proof.
