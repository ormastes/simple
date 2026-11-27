---
name: long-build
description: Coordinate long Simple builds and test matrices through finite dependency scheduling, resource monitoring, cache-preserving continuation and parallel failure repair.
---

# Long Build

Use the [shared collection policy](../../../doc/07_guide/tooling/bootstrap_failure_collection.md)
as the continuation contract.
Use its [cached object continuation workflow](../../../doc/07_guide/tooling/bootstrap_failure_collection.md#cached-object-continuation-and-early-linking)
when a failed aggregate build still has reusable successful files. Read only
the last log line, exit code and object size for successful compile observation;
inspect additional diagnostics only for failed runs.

1. Freeze the requested build/test inventory and dependencies. Record producer,
   source, runtime/tool identities, cache owners, outputs and current user worker
   preferences. Distinguish backend threads from memory-heavy frontend processes.
2. Run eligible independent rows in parallel within the selected resource
   policy. Monitor actual child progress, CPU, RSS, elapsed time and exit status;
   an idle parent waiting on a child is not proof of a stalled build.
3. Let independent jobs reach terminal results after sibling failures. Collect
   every failure and delegate distinct causes to parallel repair agents. Missing
   prerequisites block only their dependent rows.
4. For an explicit user-authorized time/memory/policy bypass, keep a separate
   monitored DIAGNOSTIC attempt with its disabled checks and retained failures.
   Do not silently reintroduce disabled enforcement through an outer wrapper.
5. On an actual restart, integrate latest requested release and reviewed
   applicable unmerged fixes into an isolated frozen source owner. Preserve
   compatible frontend/HIR/native caches and never share mutable caches between
   live writers or force identity stamps.
6. Advance a compiler lineage provisionally only after its real Hello compile
   and output execution pass. Continue full verification independently, restoring
   normal gates before formal promotion.
7. Finish the finite graph with truthful PASS/FAILED/BLOCKED/SKIPPED rows and
   actual test counts. Reuse green results for unchanged inputs; stop at
   convergence and never run an indefinite identical retry loop.

## Serialized native diagnosis

Apply [native staging and terminal evidence](../../../doc/07_guide/tooling/bootstrap_native_staging.md)
when the selected lane requires one compiler/thread. Keep the lock through owned
child cleanup and archival; publish terminal status only after fallback/finalization
completes. Source repair may remain parallel under separate ownership.

## Unified Phase 3 / Phase 4 Build & Fast Path Verification

Coordinate Phase 3 and Phase 4 builds through the canonical shared workflow in
[shared Phase 3/4 build](../../../doc/07_guide/tooling/phase3_phase4_shared_build.md)
and [bootstrap options](../../../doc/07_guide/tooling/bootstrap_options.md):

- **One cross-platform script (`scripts/bootstrap/build-phase3-phase4.sh` & `.bat`):**
  Shared across **Linux, macOS, FreeBSD, Windows (Git-Bash/MSYS2), and SimpleOS**.
  Displays the **interactive Phased Build Menu** when invoked interactively without
  `--phase=...` (or with `--menu`), and accepts non-interactive `--phase=p3a|p3|p4|all`.
  Windows `scripts/bootstrap/build-phase3-phase4.bat` delegates to `.sh` with 2 configs:
  **`mingw` DEFAULT** (`--win-config=mingw`, `llvm-mingw` clang + `ld.lld`) and
  **`msvc` optional** (`--win-config=msvc`, `clang-cl`). Deprecated standalone scripts
  (`p3-selfbuild-stage3.shs`, `p3-manual-link-stage3.shs`, `p3-smoke-stage3.shs`,
  `p3-targeted-stage2-build.shs`, `p3-entry-groups.shs`, etc.) pause with migration
  instructions for `build-phase3-phase4.sh` and return without building.
- **Default Phase 1 & Phase 2 skip once Phase 3+ exists:** In
  `scripts/bootstrap/bootstrap-from-scratch.sh --bootstrap-receipt=<receipt>`,
  when a working native pure-Simple Phase 3+ host compiler already exists
  (`bin/release/<triple>/simple` or `bin/simple` without the Rust-seed banner),
  default bootstrap skips Phase 1 (Cargo Rust seed) and Phase 2 (`seed -> stage2`)
  and delegates directly to `build-phase3-phase4.sh` (`P3 -> P4`;
  `sh scripts/bootstrap/build-phase3-phase4.sh` is the direct interactive/CLI phased
  entrypoint for Stage 3 & Stage 4). Pass `--from-seed` / `--cold-bootstrap` (or
  `--full-bootstrap` in CI) ONLY when intentionally rebuilding Phase 1 & 2 from the
  Rust seed; pass `--skip-seed` to require an existing Phase 3+ compiler without
  seed fallback.
- **Shard default, `native_host_match`, and minimal unit link:**
  `--compile-mode=shard` is **DEFAULT** in `build-phase3-phase4.sh`
  (`SIMPLE_FILE_WORKERS=0`, `SIMPLE_HIR_SHARDING=1`, `SIMPLE_MIR_SHARDING=1`);
  `--compile-mode=file` (`SIMPLE_FILE_WORKERS=1`) is optional.
  `scripts/bootstrap/stage3-native-host-link-policy.{sdn,shs}` enforces mandatory
  **`native_host_match`** (`target (platform, cpu) == host (os, arch)`), linking
  `simple` from thin entry + static `libsimple-primitive-<platform>-<cpu>.a` +
  dead-stripped primitive C core plus dynamic
  `lib/libsimple-{std,compiler-common,compiler,app}.dylib` (`.so`). Phase 3 builds
  ONLY native host targets — non-native backends (other CPUs, VHDL, GPU/CUDA/Vulkan,
  Wasm) are NOT built in Phase 3, while pre-existing `.dylib` plugins on disk remain
  loadable via `--backend-plugin <existing.dylib>`.
- **Phase 4 dual-mode build:** Phase 4 builds **both** optimized release `simple`
  (`--profile=prod --release --strip`) AND XRay-instrumented debug `simple-debug`
  (`--profile=dev --debug --no-strip --xray`), plus Stage 5 essentials
  (`simple_test_runner`, `simple_build_runner`, `simple_mcp_server`,
  `simple_lsp_mcp_server`).
- **Protected script guard & sub-second `--path-check`:** Core bootstrap scripts
  carry the `PROTECTED BOOTSTRAP SCRIPT — DO NOT MODIFY UNLESS EXPLICITLY REQUESTED BY USER`
  banner. Before launching a long build, run
  `sh scripts/check/fast-verify-bootstrap-scripts.shs` to verify sealed `.sdn` SHA-256
  digests, protected banners, syntax, and `check-bootstrap-path-matrix-all.shs`
  (`PATH_ACTION|...|status=ALIVE` superset records across Unix/Windows/SimpleOS)
  without running compilation.
