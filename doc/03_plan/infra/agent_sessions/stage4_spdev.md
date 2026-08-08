# Lane: stage4 / $sp_dev remake plan (ex-codex 019f9c04)
Goal: "$sp_dev remake plan; do all item tasks in parallel."
Last state: parser ambiguity in `src/compiler/70.backend/backend/vulkan_backend.spl` was patched by replacing `if ... else` expression-form branches with explicit `if ... return` blocks.
Current status: stage4 native-build now reaches parse completion; no parser errors from `vulkan_backend.spl`.
Blocking: stage4 consistently crashes with segmentation fault during phase3 hir lowering (`[hir-lower] lower_expr:kind`) after `phase3:hir_typecheck` begins, exit code 139.

Parallel execution split is now defined in
[`doc/03_plan/agent_tasks/stage4_spdev.md`](doc/03_plan/agent_tasks/stage4_spdev.md)
with Team A–D lanes and merge/final-review ownership.

Recent commands:
- Ran direct stage4 native-build command with `SIMPLE_NATIVE_BUILD_THREADS=4`; logs: `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage4-native-build-current.log`; result `EXIT:139`.
- Ran same command with `SIMPLE_NATIVE_BUILD_THREADS=1` (to exclude concurrency effects); logs: `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage4-native-build-threads1.log`; result `EXIT:139`.

Next: classify phase3 `hir_lower` segfault and either bisect or escalate with compiler/runtime team; do not re-run full native-build until blocker is isolated/fixed.

## 2026-08-08 continuation evidence

The historical phase-3 crash above is superseded for the isolated x86 lane in
`/tmp/simple-stage4-clean.SxuiW8`. The retained-cache Cranelift Stage4 command
now compiles and links a full CLI candidate with `SIMPLE_NO_STUB_FALLBACK=1`.
The latest successful build log is
`build/st4-clean/logs/stage4-incremental-direct-interpret-closure.log`.

Pushed integration evidence:

- `57f0eb775eb` fixes the missing SIMD lint helper import and prevents the HTML
  tokenizer's private substring helper from sharing the flat native symbol.
- `6feea713849` binds staged HIR call arguments to typed `CallArg` locals before
  field access. The focused probes changed from nil-receiver plus SIGILL 132 to
  structured HIR errors, and the source regression now covers primitive casts
  plus both `range` arguments.
- Integration branch:
  `codex/stage4-x86-phase4-llvm23-integrated`.

Current x86 blocker:

- `interpret_file` loads only an external entry file, so imported modules are
  absent from `ModuleSurface` and imported callees remain unresolved.
- Activating the existing native entry-closure walker for direct interpretation
  exposes a separate compiled-Stage4 nil-field/SIGILL inside that closure path.
- Three incremental resolver cycles were exhausted. The unproven closure change
  was removed; do not repeat the same candidate build. Next diagnosis must isolate
  the closure walk with typed staged-container access before another retry.
- Essential-tools smoke is therefore not yet a PASS. Stage4 link and `--version`
  are evidence only, not x86 admission.

Platform evidence:

- `sh scripts/check/check-simpleos-x86-64-wm-qemu-preflight.shs` passed on
  2026-08-08. It proved entry/theme/SIMD host readiness and explicitly reported
  `simpleos_x86_64_wm_qemu_preflight_live_qemu=not-started-host-gate`.
- No fresh live SimpleOS, FreeBSD, AArch64, RISC-V, or macOS ARM receipt exists.
  The next platform command is the canonical FreeBSD smoke wrapper, not a full
  bootstrap: `sh scripts/check/check-freebsd-bootstrap-qemu.shs --smoke`.

Proposed provider-capsule direction (not yet implemented or admitted):

- Stage4 external SFFI inputs must be archive/shared-library providers bound by
  canonical path, SHA-256, target, backend, runtime bundle, producer hash, and
  symbol-contract hash.
- Strict Stage4 must reject raw `.o`/`.obj`, core runtime identities, compiler
  backfill, duplicate strong ownership, stale hashes, and wrong targets.
- Bind the ordered provider-set hash into Stage4 candidate provenance and the
  link-profile fingerprint. Do not expose raw `runtime_legacy_core.o` through
  `SIMPLE_LINK_OBJECTS`.
