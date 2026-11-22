---
name: bootstrap
description: Build and advance Simple compiler generations across LLVM or Cranelift with real Hello execution, immutable lineage, isolated caches and honest provisional qualification.
---

# Bootstrap

For release compiler selection, apply the
[phase ladder producer-selection policy](../../../doc/07_guide/infra/toolchain/phase_ladder_ci.md#release-producer-selection)
before starting or resuming a phase build.

Read the [bootstrap rules](../../../.claude/rules/bootstrap.md) and the
[shared collection policy](../../../doc/07_guide/tooling/bootstrap_failure_collection.md).
Use [parallel handoff](../../../doc/07_guide/app/llm/bootstrap_parallel_handoff.md)
for required evidence and formal promotion boundaries.
For tagged source workarounds, failed-file retries, independent object collection
and early manual linking, apply the shared
[cached object continuation workflow](../../../doc/07_guide/tooling/bootstrap_failure_collection.md#cached-object-continuation-and-early-linking).

- Identify which compiler builds each phase and bind its actual bytes, source,
  runtime and tools. The Rust seed is bootstrap-only; do not substitute it for
  claimed self-hosted executable behavior.
- Keep LLVM/Cranelift and independent module/test rows running in parallel when
  requested. Collect failures to the end of the finite runnable graph, then
  delegate separate causes to repair agents with private writable caches.
- Require the exact new compiler to compile Hello World and require that output
  executable to run correctly before starting a dependent provisional phase.
  Full qualification may continue concurrently; label descendants unadmitted.
- For a requested four-binary Hello linkage sanity, use the campaign runner
  and verify direct source, two-object, static-library and shared-library
  executables. Run independent jobs in parallel when requested, with distinct
  outputs and logs and writer-safe caches. Phase 1 requires interpreter and
  skips BuildRunner; phase 2 skips interpreter and requires BuildRunner; phase 3
  requires both. See [parallel handoff](../../../doc/07_guide/app/llm/bootstrap_parallel_handoff.md#four-executable-hello-linkage-sanity).
- Record user-authorized diagnostic checker bypasses and retain resource/progress
  monitoring, failed receipts and actual identities. Missing artifacts, invalid
  inputs and zero executed tests never become PASS. Restore normal gates before
  admission, deployment or release.
- Preserve live frozen builds. At the next actual restart, fetch requested
  release and integrate reviewed applicable unmerged fixes; reuse compatible
  frontend/HIR/native caches with explicit invalidation where required.
- Build each requested producer's full CLI and test runner before claiming
  suite execution. Report executable output and positive assertion counts,
  not merely successful linking. Reuse unchanged green evidence and respect
  finite per-cause repair budgets and recorded user exceptions.

## Native staging and finality

For serialized crash diagnosis, host CUDA policy, RAM cache-parent staging and
terminal consumer authority, apply [native staging and terminal evidence](../../../doc/07_guide/tooling/bootstrap_native_staging.md).
Keep campaign Phase 3 priority and full-CLI test ownership explicit; source review
and a linked bootstrap binary do not admit suite execution.

## Unified Phase 3 / Phase 4 Architecture (2026-11-22)

See [shared Phase 3/4 build](../../../doc/07_guide/tooling/phase3_phase4_shared_build.md)
and [bootstrap options](../../../doc/07_guide/tooling/bootstrap_options.md) for the
canonical cross-platform workflow:

- **Shared cross-platform phased script:** `scripts/bootstrap/build-phase3-phase4.sh`
  drives Phase 3 and Phase 4 across **Linux, macOS, FreeBSD, Windows (Git-Bash/MSYS2),
  and SimpleOS**. Running interactively without `--phase=...` (or with `--menu`) opens
  the **interactive Phased Build Menu**; non-interactive automation uses
  `--phase=p3a|p3|p4|all`. On Windows, `scripts/bootstrap/build-phase3-phase4.bat`
  delegates to the same `.sh` script with 2 configs: **`mingw` is DEFAULT**
  (`--win-config=mingw`, `llvm-mingw` clang + `ld.lld`) and **`msvc` is optional**
  (`--win-config=msvc`, `clang-cl`). Legacy standalone scripts
  (`p3-selfbuild-stage3.shs`, `p3-manual-link-stage3.shs`, `p3-smoke-stage3.shs`,
  `p3-targeted-stage2-build.shs`, `p3-entry-groups.shs`, etc.) are deprecated —
  direct invocation pauses with migration instructions for `build-phase3-phase4.sh`
  (including phased/shard mode) and returns without building.
- **Default bootstrap skips Phase 1 & Phase 2 when Phase 3+ exists:** In
  `scripts/bootstrap/bootstrap-from-scratch.sh --bootstrap-receipt=<receipt>`,
  when a working native pure-Simple Phase 3+ host compiler already exists
  (`bin/release/<triple>/simple` or `bin/simple` without the Rust-seed banner),
  default bootstrap skips Phase 1 (Cargo Rust seed) and Phase 2 (`seed -> stage2`)
  and delegates directly to `scripts/bootstrap/build-phase3-phase4.sh` (`P3 -> P4`;
  `sh scripts/bootstrap/build-phase3-phase4.sh` is the direct interactive/CLI phased
  entrypoint for Stage 3 & Stage 4). Pass `--from-seed` / `--cold-bootstrap` (or
  `--full-bootstrap` in CI) ONLY when intentionally rebuilding Phase 1 & Phase 2
  from the Rust seed; pass `--skip-seed` to require an existing Phase 3+ compiler
  without seed fallback.
- **Compile mode (`shard` default, `file` optional) & `native_host_match` link policy:**
  `--compile-mode=shard` is **DEFAULT** in `build-phase3-phase4.sh`
  (`SIMPLE_FILE_WORKERS=0`, `SIMPLE_HIR_SHARDING=1`, `SIMPLE_MIR_SHARDING=1`);
  `--compile-mode=file` (`SIMPLE_FILE_WORKERS=1`) is optional (reconciling the
  2026-10-25 historical note below, which applies only to unconfigured standalone
  `native-build` when `SIMPLE_FILE_WORKERS` is unset).
  `scripts/bootstrap/stage3-native-host-link-policy.{sdn,shs}` enforces the mandatory
  **`native_host_match` tag check** (`target (platform, cpu) == host (os, arch)`),
  minimizing `simple` to link **only** thin entry + `(platform, cpu)` static primitive
  archive (`libsimple-primitive-<platform>-<cpu>.a`) + dead-stripped primitive C core
  statically while linking `lib/libsimple-{std,compiler-common,compiler,app}.dylib`
  (`.so`) dynamically. **Phase 3 builds ONLY native host targets** — non-native
  backends (other CPUs, VHDL, GPU/CUDA/Vulkan, Wasm) are NOT built during Phase 3,
  but if a `.dylib` already exists on disk `simple` can load and use it
  (`--backend-plugin <existing.dylib>`).
- **Phase 4 dual-mode build:** Phase 4 builds **both** the optimized production
  binary (`simple`: `--profile=prod --release --strip`) AND the XRay-instrumented
  debug binary (`simple-debug`: `--profile=dev --debug --no-strip --xray`), plus
  Stage 5 essentials (`simple_test_runner`, `simple_build_runner`,
  `simple_mcp_server`, `simple_lsp_mcp_server`).
- **Protected script guard & zero-compile `--path-check`:** Every core bootstrap
  script carries a top-of-file
  `PROTECTED BOOTSTRAP SCRIPT — DO NOT MODIFY UNLESS EXPLICITLY REQUESTED BY USER`
  banner. Run `sh scripts/check/fast-verify-bootstrap-scripts.shs` for a sub-second
  check of sealed `.sdn` SHA-256 digests, protected banners, syntax, and
  `check-bootstrap-path-matrix-all.shs` across Unix/Windows/SimpleOS using extensible
  `PATH_ACTION|...|status=ALIVE` superset records without running compilation.

## Historical note (2026-10-25; script default superseded by `--compile-mode=shard` above)

Shard knobs, frozen-Stage-2 Stage 3, `.spab`/DigestV1 cache protocol and Lean
cache gates: [bootstrap options](../../../doc/07_guide/tooling/bootstrap_options.md).
*(Note: standalone compiler driver `NATIVE_PER_FILE_PIPELINE_DEFAULT_V1="1"` below applies only when `SIMPLE_FILE_WORKERS` is unset outside bootstrap scripts; `build-phase3-phase4.sh` defaults to `--compile-mode=shard` / `SIMPLE_FILE_WORKERS=0`.)*
Per-file src to obj in standalone `native-build` (#4525 compiler, #4542 guide, scripts PR 2026-10-25): each module lowers to its own `aot-<hash>.o` in the per-module object cache under `SIMPLE_NATIVE_BUILD_CACHE_DIR`, codegen fans out over `SIMPLE_NATIVE_BUILD_THREADS` (scripts: host.sdn `max_build_jobs`), then all objects link into one binary. Stage 3 scripts pass `SIMPLE_BOOTSTRAP=` empty so the bootstrap_fixed shortcut is not forced; `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1` opts back into the whole-program lane (hashed into the Stage 3 args). First-object proof: 9-module closure, 9 objects, first at 160 s, last at 174 s, binary runs. Never `git stash`.
