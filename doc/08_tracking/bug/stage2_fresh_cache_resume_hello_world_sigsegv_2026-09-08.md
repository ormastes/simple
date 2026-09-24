# Fresh Stage 2 cache resume: hello-world admission SIGSEGV

Status: fresh-output wrapper fixed; canonical compiler admission fails.

The previous wrapper reused `build/macos-stage4-deploy` and canonical
bootstrap refused `stale-evidence-output-root`. Astra changed the wrapper to
validate and copy only the native cache into a new output, holding the old
output's canonical lock throughout the copy. The production clone helper's
behavioral regression passes, including independent writable files, matching
source-before/source-after/copy manifests, old-evidence exclusion, and refusal
of symlinks or missing ownership.

## One canonical attempt

- Command: `sh scripts/bootstrap/resume-stage2-from-cache.sh
  /Users/ormastes/macos-stage4-codex-20260908/build/macos-stage4-deploy`
- Fresh output: `build/stage2-resume.bphEaB`.
- Invocation log: `/tmp/simple-stage2-astra-fresh-20260908.log`.
- Bootstrap PID: `92120`; native compiler PID: `1478`. Both exited;
  tool session `45624` returned exit `1`.
- Current Rust authority fingerprint:
  `300d1ae840e57247df87f52cce95e5888d7e06fb3046450eed46a004ee0e0369`.
  Canonical bootstrap verified it and skipped rebuilding Rust.
- Copied cache manifest SHA-256:
  `79903b85d07fd72ebba2f52ebb77926ef63bab6e010693fccd68b41c77b70815`.
- Stage 2 native build: `883 compiled, 0 cached, 0 failed`;
  `418.4s compile + 10.5s link = 428.9s total`.
- Candidate: arm64 Mach-O, `139096296` bytes, retained only as
  `build/stage2-resume.bphEaB/stage2/aarch64-apple-darwin/simple.rejected`.
- Candidate SHA-256:
  `39dab72ae750c3974dfb6b5df370aa69466e17365f712d5e89d564346c589155`.

The old cache was transported correctly, but the current source/producer
fingerprint selected a new scope, so this run reused zero compiled objects.
That is the expected provenance boundary, not a reason to alter cache keys.

## New failure

Canonical sanity passed version and unsupported-command checks. Its ordinary
frontend pass completed `p2_add`, `stage2_mir_retention`, and
`stage2_module_path_naming` with raw status `0`. It then failed the positional
hello-world native build with raw status `139`. The bounded collector records
`status=complete`, `reason=child-signal`, `bytes_captured=4995`; this was not
a timeout. The final compiler event was MIR completion for
`scripts.check.cert.redeploy_gate.fixtures.hello_world` at `elapsed_ms=812`.
That locates the last observed phase, not a proven crash cause.

Authoritative evidence, relative to the fresh output:

- `logs/aarch64-apple-darwin/stage2-native-build.log`
- `stage3/aarch64-apple-darwin/stage2-sanity.env`
- `stage3/aarch64-apple-darwin/stage2-sanity.env.frontend-bootstrap-0.status.env`
- `stage3/aarch64-apple-darwin/stage2-sanity.env.frontend-bootstrap-0.log.hello-world-positional`
- `stage3/aarch64-apple-darwin/stage2-sanity.env.frontend-bootstrap-0.log.hello-world-positional.bounded.env`

The hello-world log SHA-256 is
`9ebfb96620b485a37c80ffa37dd24d32386f635a931357267f44e6995d1c8109`.
Candidate hashes before and after sanity match. No admission receipt or
canonical Chrome dylib was published, and no second canonical attempt ran.

The next compiler investigation should use this exact candidate and bounded
hello-world failure as diagnostic input to obtain the crash location before
any further full rebuild. The Chrome producer remains unadmitted.

## LLDB diagnosis and narrow source repair (2026-09-09)

The exact positional invocation was reproduced against the retained candidate
under LLDB with `SIMPLE_BOOTSTRAP=0`, backend `llvm`, runtime bundle
`core-c-bootstrap`, `--entry-closure`, `--mode one-binary`, and the same
fixture path. The failure is deterministic and occurs immediately after the
MIR phase, with no worker timeout.

Crash evidence:

- stop reason: `EXC_BAD_ACCESS (code=1, address=0x30)`
- PC: `0x1004699b4`
- symbol: `compiler__mir_opt__mir_opt__mod__optimizationpipeline_for_backend + 180`
- faulting instruction: `ldr x0, [x8, #0x30]`, with `x8=0`
- thread: `#1`, `com.apple.main-thread`
- stack: `optimizationpipeline_for_backend` ->
  `optimize_module_for_backend` -> `CompilerDriver.optimize_mir_level` ->
  `CompilerDriver.aot_compile` -> `CompilerDriver.compile_with_reverse_reference_owner_v1`
  -> `CompilerDriver.compile` -> `run_native_build_bootstrap` -> `main`
- candidate remained unchanged: SHA-256
  `39dab72ae750c3974dfb6b5df370aa69466e17365f712d5e89d564346c589155`

The source defect was the bootstrap-unsafe conjunction
`descriptor.? and ... descriptor.unwrap()` in
`src/compiler/60.mir_opt/mir_opt/mod.spl`. The seed can treat a tagged nil
optional as truthy, so `unwrap()` reached a null payload. The function now
matches `Some(d)`/`nil` explicitly and reads `d` only in the `Some` arm,
failing closed for unknown pass names.

Focused evidence:

- `src/compiler_rust/target/bootstrap/simple run
  test/01_unit/compiler/mir/optimization_pipeline_option_match_spec.spl`
  passed 2/2.
- `src/compiler_rust/target/bootstrap/simple check
  src/compiler/60.mir_opt/mir_opt/mod.spl` reached the source-check path but
  reported the known infrastructure blocker: no admitted cached self-hosted
  check worker artifact. No Stage 2 rebuild was run after the repair.

## Second fresh candidate: distinct backend-selector failure (2026-09-09)

The later canonical output `build/stage2-resume.WBRMDQ` also returned raw 139,
but its native backtrace advances past optimization to
`select_static_backend_v1 +200`, address `0x10`. The caller omitted a dynamic
default table argument, and the positional bootstrap route also skipped K1
registry installation. Both source boundaries have a focused repair; a native
ABI regression passes, while complete Stage 2 admission remains pending.
See [the exact diagnosis and verification limits](stage2_backend_selector_missing_table_argument_2026-09-09.md).
