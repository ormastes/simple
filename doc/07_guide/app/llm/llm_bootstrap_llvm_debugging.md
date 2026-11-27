# Bootstrap LLVM Failure Debugging

Use this workflow when a native bootstrap fails during LLVM generation. Rust is
only the seed in this workflow: seed diagnostics may explain why generation
stopped, but success is proved only by the resulting pure-Simple compiler.

## Finish collection and repair in parallel

Follow the [shared collection policy](../../tooling/bootstrap_failure_collection.md).
Always finish independently runnable modules and tests; one failed backend or
entry must not cancel healthy sibling work. Group collected failures by their
first actionable cause and assign separate agents to logic, performance and
resource-policy defects with isolated writable caches/source scopes.

A user-authorized time, memory or other checker exception is an explicitly
labeled DIAGNOSTIC attempt with resource/progress monitoring and the original
failed receipt retained. Record exactly which check is disabled; keep other
limits visible. Do not infer an oversized input merely from a generic error
label, or claim the exception repairs the underlying defect. Formal admission
and release still require restored checks and truthful evidence.

Before advancing provisionally, the exact produced compiler must compile Hello
World and successfully execute its output. Full qualification need not finish
first. On the next actual restart use the requested latest release plus reviewed
applicable unmerged fixes, freeze identities, and reuse only compatible persisted
frontend/HIR/native caches. Never alter live builds or retry identical failures
indefinitely; continue the remaining finite work graph instead.

## Unified Phase 3 / Phase 4 Build, XRay Debug Binary & Alive Path Check

Drive native Phase 3 / Phase 4 reproduction and recovery through the shared
cross-platform script in [shared Phase 3/4 build](../../tooling/phase3_phase4_shared_build.md)
and [bootstrap options](../../tooling/bootstrap_options.md):

- **Shared cross-platform phased build (`scripts/bootstrap/build-phase3-phase4.sh` & `.bat`):**
  One script across **Linux, macOS, FreeBSD, Windows (Git-Bash/MSYS2), and SimpleOS**.
  Displays the **interactive Phased Build Menu** when invoked interactively without
  `--phase=...` (or with `--menu`), and accepts non-interactive `--phase=p3a|p3|p4|all`.
  Windows `scripts/bootstrap/build-phase3-phase4.bat` delegates to `.sh` with 2 configs:
  **`mingw` DEFAULT** (`--win-config=mingw`, `llvm-mingw` clang + `ld.lld`) and
  **`msvc` optional** (`--win-config=msvc`, `clang-cl`). Legacy standalone scripts
  (`p3-selfbuild-stage3.shs`, `p3-manual-link-stage3.shs`, `p3-smoke-stage3.shs`,
  `p3-targeted-stage2-build.shs`, `p3-entry-groups.shs`, etc.) are deprecated —
  direct invocation pauses with migration instructions for `build-phase3-phase4.sh`
  (including phased/shard mode) and returns without building.
- **Default Phase 1 & Phase 2 skip once Phase 3+ exists:** In
  `scripts/bootstrap/bootstrap-from-scratch.sh`, when a working native pure-Simple
  Phase 3+ host compiler already exists (`bin/release/<triple>/simple` or `bin/simple`
  without the Rust-seed banner), default bootstrap skips Phase 1 (Cargo Rust seed)
  and Phase 2 (`seed -> stage2`) and delegates directly to
  `scripts/bootstrap/build-phase3-phase4.sh` (`P3 -> P4`). Pass `--from-seed` /
  `--cold-bootstrap` (or `--full-bootstrap` in CI) ONLY when intentionally rebuilding
  or debugging Phase 1 & Phase 2 from the Rust seed; pass `--skip-seed` to require
  an existing Phase 3+ compiler without seed fallback.
- **Compile mode (`shard` default, `file` optional) & `native_host_match` link policy:**
  `--compile-mode=shard` is **DEFAULT** in `build-phase3-phase4.sh`
  (`SIMPLE_FILE_WORKERS=0`, `SIMPLE_HIR_SHARDING=1`, `SIMPLE_MIR_SHARDING=1`);
  `--compile-mode=file` (`SIMPLE_FILE_WORKERS=1`) is optional.
  `scripts/bootstrap/stage3-native-host-link-policy.{sdn,shs}` enforces mandatory
  **`native_host_match`** (`target (platform, cpu) == host (os, arch)`), linking
  `simple` from thin entry + `(platform, cpu)` static primitive archive
  (`libsimple-primitive-<platform>-<cpu>.a`) + dead-stripped primitive C core plus
  dynamic `lib/libsimple-{std,compiler-common,compiler,app}.dylib` (`.so`).
  **Phase 3 builds ONLY native host targets** — non-native backends (other CPUs,
  VHDL, GPU/CUDA/Vulkan, Wasm) are NOT built during Phase 3, **but if a `.dylib`
  already exists on disk, `simple` can load and use it** (`--backend-plugin <existing.dylib>`).
- **Phase 4 dual-mode build (`--xray` + optimized release):** Phase 4 builds **both**
  the optimized production binary (`simple`: `--profile=prod --release --strip`) AND
  the XRay-instrumented debug binary (`simple-debug`: `--profile=dev --debug --no-strip --xray`,
  preserving debug symbols and XRay sleds for crash/latency diagnosis), plus Stage 5
  essentials (`simple_test_runner`, `simple_build_runner`, `simple_mcp_server`,
  `simple_lsp_mcp_server`).
- **Protected script guard & zero-compile `--path-check`:** Every core bootstrap
  script carries a top-of-file
  `PROTECTED BOOTSTRAP SCRIPT — DO NOT MODIFY UNLESS EXPLICITLY REQUESTED BY USER`
  banner. Run `sh scripts/check/fast-verify-bootstrap-scripts.shs` for a sub-second
  check of sealed `.sdn` SHA-256 digests, protected banners, syntax, and
  `check-bootstrap-path-matrix-all.shs` (`PATH_ACTION|...|status=ALIVE` superset
  records across Unix/Windows/SimpleOS) before launching heavy LLVM debug runs.

## Diagnose the earliest broken boundary

Classify the failure before changing a backend:

1. An incorrect resolved owner in HIR is a name-resolution/lowering defect.
2. A `GlobalLoad` without a declared source global in MIR is a semantic-lowering
   defect. Do not make LLVM invent or accept that global.
3. Textual IR rejected by `llvm-as` is malformed LLVM generation.
4. Bitcode rejected by `opt -passes=verify` is an LLVM validity defect.
5. Verified bitcode rejected by `llc` is a target/code-generation defect.

For a seed-assisted Stage 4 build, preserve failure artifacts without changing
the normal output path:

```bash
SIMPLE_LLVM_DIAGNOSTIC_DIR=build/bootstrap/llvm-diagnostics \
  <stage3-simple> native-build <the-existing-stage4-arguments>
```

On a seed LLVM failure this writes partial `.ll` and `.bc`, the MIR debug form,
and an error receipt. Partial artifacts may be intentionally invalid because
generation stopped at the first semantic error; replaying them makes that LLVM
boundary independently visible while the MIR and receipt explain the earlier
semantic boundary.

To preserve complete `.ll`, `.bc`, and MIR for every successfully generated
module as well, add `SIMPLE_LLVM_DIAGNOSTIC_MODE=all`. This mode intentionally
adds I/O and disk usage, so use the default failure-only mode for fast bootstrap
retries.

The primary pure-Simple diagnostic mode exercises the actual Simple LLVM text
backend and an explicit LLVM boundary:

```bash
SIMPLE_LLVM_BITCODE_DEBUG=1 SIMPLE_KEEP_LLVM_IR=1 \
  <pure-simple> native-build --backend llvm <the-existing-build-arguments>
```

For every module, pure Simple emits textual `.ll`, `llvm-as` assembles `.bc`,
`opt -passes=verify` checks the bitcode, and `llc` compiles that bitcode to an
object. The reported stage and retained paths distinguish a Simple text-emitter
bug from invalid LLVM bitcode or a target backend failure.

Replay complete text IR or bitcode independently:

```bash
sh scripts/check/replay-llvm-artifact.shs module.ll build/check/llvm-replay
sh scripts/check/replay-llvm-artifact.shs module.bc build/check/llvm-replay
```

The replay performs text-to-bitcode assembly when needed, LLVM verification,
and object generation. It reports the exact failing stage and retains generated
bitcode/object files. Never treat replay success as Stage 4 success: build the
pure-Simple executable, pass the Hello compile/run gate, and finish the required
sanity, essential-tool and formal admission checks before deployment.

## Close recovery with the Phase 4 system gate

After an admitted pure-Simple Stage 3 produces a current-source full CLI, use
the exact candidate and adjacent provenance with
`test/03_system/compiler/phase4_compiler_debug_recovery_spec.spl`. Configure
`PHASE4_DEBUG_CANDIDATE`, `PHASE4_DEBUG_PROVENANCE`,
`PHASE4_DEBUG_DEPLOYED`, and a lane-owned `PHASE4_DEBUG_ARTIFACT_ROOT` as
documented in
`doc/03_plan/sys_test/phase4_compiler_debug_recovery.md`.

The system gate reuses the post-bootstrap admission checker, then checks the
compiler, library, MCP, and LSP trees; executes the MCP stdio integration;
native-builds the C5 character ABI fixture and requires exit `42`; requires an
explicit canonical DAP PASS and rejects SKIP; and proves the installed binary
hash equals the admitted candidate. Missing Stage 4 authority is
`TEST_BLOCKED`. Never run this acceptance surface with the Rust seed or count a
diagnostic replay as runtime PASS.
