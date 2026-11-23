# Bootstrap options, shard knobs and cache protocol state

Dated 2026-10-25 against `release/1.0.0`, reconciled 2026-11-22 for the unified
Phase 3 / Phase 4 build architecture. Each item names the PR or file it was
checked against:

- **Bootstrap scripts (`scripts/bootstrap/build-phase3-phase4.sh`, `.bat`, and `config/bootstrap.sdn`):**
  **`--compile-mode=shard` is DEFAULT** (`SIMPLE_FILE_WORKERS=0`, `SIMPLE_HIR_SHARDING=1`,
  `SIMPLE_MIR_SHARDING=1`); **`--compile-mode=file` is optional** (`SIMPLE_FILE_WORKERS=1`).
- **Standalone direct `simple native-build` (outside bootstrap scripts):** when
  `SIMPLE_FILE_WORKERS` is left unset in the environment, the internal driver constant
  `NATIVE_PER_FILE_PIPELINE_DEFAULT_V1 = "1"` (2026-11-04) selects the per-file worker
  pool; `SIMPLE_FILE_WORKERS=0` opts out. See the standalone driver section below.

## Shared Cross-Platform Phase 3 & Phase 4 Script (`scripts/bootstrap/build-phase3-phase4.sh`)

**Linux, macOS, FreeBSD, Windows (Git-Bash/MSYS2), and SimpleOS** share a single phased build entrypoint:
- **POSIX / Bash (Linux, macOS, FreeBSD, Windows Git-Bash/MSYS2, SimpleOS):** `scripts/bootstrap/build-phase3-phase4.sh`
- **Windows Batch wrapper (2 configs delegating to the same `.sh` script — `mingw` DEFAULT, `msvc` optional):** `scripts/bootstrap/build-phase3-phase4.bat` (`--win-config=mingw` uses `llvm-mingw` clang + `ld.lld` by default; `--win-config=msvc` uses `clang-cl`)
- **Platform/CPU policy & `native_host_match` tag gate:** `scripts/bootstrap/stage3-native-host-link-policy.sdn` + `scripts/bootstrap/stage3-native-host-link-policy.shs`

Key architectural behaviors:
- **Interactive Phased Build Menu & Non-Interactive Phases:** Run `sh scripts/bootstrap/build-phase3-phase4.sh --menu` (or invoke interactively without `--phase=...`) to open the interactive Phased Build Menu, or pass non-interactive `--phase=p3a|p3|p4|all`.
- **Default Bootstrap Skips Phase 1 & Phase 2 Once Phase 3+ Exists:** In `scripts/bootstrap/bootstrap-from-scratch.sh`, when a working native pure-Simple Phase 3+ host compiler already exists (`bin/release/<triple>/simple` or `bin/simple` without the Rust-seed banner), **default bootstrap skips Phase 1 (Cargo Rust seed) and Phase 2 (`seed -> stage2`)** and delegates directly to `scripts/bootstrap/build-phase3-phase4.sh` (`P3 -> P4`). Pass `--from-seed` / `--cold-bootstrap` (or `--full-bootstrap` in CI) ONLY when intentionally rebuilding Phase 1 & Phase 2 from the Rust seed; pass `--skip-seed` to require an existing Phase 3+ compiler without seed fallback.
- **Shard Build Default, File-Based Optional:** `--compile-mode=shard` is **DEFAULT** in `build-phase3-phase4.sh` (phase-based HIR/MIR shard build: `SIMPLE_FILE_WORKERS=0`, `SIMPLE_HIR_SHARDING=1`, `SIMPLE_MIR_SHARDING=1`); `--compile-mode=file` is optional (parallel per-file worker pool: `SIMPLE_FILE_WORKERS=1`).
- **Platform/CPU Static-Primitive + Dynamic Unit Link (`native_host_match`):** Enforces mandatory **`native_host_match` tag check** (`target (platform, cpu) == host (os, arch)`), minimizing `simple` to link **only** thin entry + `(platform, cpu)` static primitive archive (`libsimple-primitive-<platform>-<cpu>.a`) + dead-stripped primitive C core statically, while linking `lib/libsimple-{std,compiler-common,compiler,app}.dylib` (`.so`) dynamically. **Phase 3 builds ONLY native host targets** — non-native backends (other CPUs, VHDL, GPU/CUDA/Vulkan, Wasm) are NOT built during Phase 3, **but if a `.dylib` already exists on disk, `simple` can load and use it** (`--backend-plugin <existing.dylib>`).
- **Phase 4 Dual-Mode Build (`--xray` + Optimized Release):** Phase 4 builds **both** the optimized production binary (`simple`: `--profile=prod --release --strip`) AND the XRay-instrumented debug binary (`simple-debug`: `--profile=dev --debug --no-strip --xray`), plus Stage 5 essentials (`simple_test_runner`, `simple_build_runner`, `simple_mcp_server`, `simple_lsp_mcp_server`).
- **Zero-Compile `--path-check` Alive Verification & Protected Script Guard:** Every core bootstrap script carries a top-of-file `PROTECTED BOOTSTRAP SCRIPT — DO NOT MODIFY UNLESS EXPLICITLY REQUESTED BY USER` banner. Run `sh scripts/check/fast-verify-bootstrap-scripts.shs` for a sub-second check of sealed `.sdn` SHA-256 digests, protected banners, syntax, and `check-bootstrap-path-matrix-all.shs` across Unix/Windows/SimpleOS using extensible `PATH_ACTION|...|status=ALIVE` superset records without running actual compilation (`--path-check`, optionally with `--simulate-host=<platform>-<cpu>`).
- **Deprecated Standalone Phase 3/4 Scripts (`p3-selfbuild-stage3.shs`, `p3-manual-link-stage3.shs`, `p3-smoke-stage3.shs`, `p3-targeted-stage2-build.shs`, `p3-entry-groups.shs`, etc.):** Retained on disk for historical reference/tests, but invoking them directly pauses with migration instructions showing how to run `build-phase3-phase4.sh` (including phased/shard mode) and returns without building.

See [phase3_phase4_shared_build.md](phase3_phase4_shared_build.md) for complete CLI tables and examples.

## Standalone `native-build` driver mode: file-based src → obj + library link (historical 2026-11-04 note; bootstrap scripts default to `--compile-mode=shard`)

> **Reconciliation note (2026-11-22):** `build-phase3-phase4.sh` and `config/bootstrap.sdn` (`stage3_file_workers: 0`) default Phase 3/4 bootstrap builds to `--compile-mode=shard` (`SIMPLE_FILE_WORKERS=0`), with `--compile-mode=file` (`SIMPLE_FILE_WORKERS=1`) available as an explicit option. The `NATIVE_PER_FILE_PIPELINE_DEFAULT_V1 = "1"` constant below applies only when invoking standalone `simple native-build` directly with `SIMPLE_FILE_WORKERS` unset.

- **Standalone driver default (no flag, no env, outside bootstrap scripts):** each source file goes src → obj in ONE
  process (parse → HIR → MIR → object, like cc1) via the per-file worker
  pool; objects are then linked into the binary. Selected by
  `NATIVE_PER_FILE_PIPELINE_DEFAULT_V1 = "1"`
  (`src/compiler/80.driver/driver_build/native_file_worker_v1.spl`), pinned
  by `test/01_unit/compiler/driver/native_file_worker_v1_spec.spl`. Applies to
  unconfigured standalone `native-build` invocations (whereas `build-phase3-phase4.sh`
  explicitly sets `--compile-mode=shard` / `SIMPLE_FILE_WORKERS=0` by default).
- **Opt-outs (explicit, per invocation only):** `SIMPLE_FILE_WORKERS=0`
  (two-pass HIR-shard then MIR-shard route), `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1`
  (whole-program single-object route), `SIMPLE_MIR_SHARDING=0` (disables the
  pool and MIR sharding). Related shard knobs: `SIMPLE_PARSE_SHARDING`,
  `SIMPLE_HIR_SHARDING`, `SIMPLE_MIR_SHARD_COUNT`, `SIMPLE_MIR_SHARD_WORKER_KB`,
  `SIMPLE_HIR_SHARD_WORKER_KB`, `SIMPLE_FILE_FIBERS`.
- **Rule: never change a shared default to suit one build.** No config file,
  script-global env default, or constant flip. A launcher that needs a
  non-default mode passes the option at its own call site with a comment
  saying why (note: historical `scripts/bootstrap/p3-entry-groups.shs` is now
  deprecated and delegates migration instructions to `build-phase3-phase4.sh`).
- **Exception (2026-11-13, owner request): Stage 3 route in tracked config.**
  While the per-file route still fails on importing units (bug #8504 layers
  2-3; layer 1 fixed by #8746), `config/bootstrap.sdn` sets
  `stage3_file_workers: 0`. Precedence: non-empty `SIMPLE_FILE_WORKERS` env >
  that key > compiler default. Read by `resume-stage3-from-admitted.sh` and
  the `bootstrap-from-scratch.sh` Stage 3 (`bootstrap_select_stage3_file_workers`,
  `scripts/bootstrap/bootstrap-jobs.shs`). It is in git so a clean clone
  behaves like the owner's runs; delete the key once per-file builds Stage 3.
- **Gap (not yet default):** per-package/per-layer library archives
  (`.a`) linked into the binary. Today the pool's per-module objects are
  linked from the sealed ledger in one link; package archives exist only on
  the demand-SCC path (`driver/cache/package_archive_cache.spl`).
- Runtime verification of the flipped default (first-object time, total
  cold/warm) is **pending a stage3 binary**.
## Direct compiler or BuildRunner selection

`simple native-build ...` already compiles directly without BuildRunner. The
full CLI's ordinary `simple build ...` forwards to the same pipeline, except
named targets and special subcommands have their own dispatch. Prefer
`native-build` when supplying a compiler target triple: `build --target` selects
a named project target. A minimal bootstrap compiler need not provide `build`
or `test`.

Build scripts can select either existing owner explicitly:

```sh
# Run from the frozen source root. Use absolute, pinned program/runtime paths.
sh scripts/build/run-build.shs --executor=direct --program="$compiler" -- \
  --target aarch64-unknown-linux-gnu --backend cranelift \
  --runtime-bundle core-c-bootstrap --runtime-path "$runtime" \
  --source src/compiler --source src/app --source src/lib --source src/plugins \
  --entry-closure --entry src/app/cli/bootstrap_main.spl \
  --threads 2 --cache-dir "$private_cache" --mode dynload --output "$candidate"

# The existing BuildRunner owns manifest validation, admission and execution.
sh scripts/build/run-build.shs --executor=buildrunner --program="$buildrunner" -- \
  --manifest "$manifest" --state "$state" \
  --source-root "$frozen_source" --output-root "$output_root"
```

Select the actual host/target and source composition for the intended artifact;
the example target is AArch64 Linux, not a portable default. Required composition
roots and runtime providers remain the caller's recorded source policy. For a
test-runner binary, select its real entry (`src/app/test_runner_new/main.spl`)
and complete source/provider closure instead. TestRunner executes tests after a
build; it is not an alternative compiler backend.

`SIMPLE_BUILD_EXECUTOR=direct|buildrunner` configures a script default; explicit
`--executor=` wins. Unset defaults to `direct`; invalid or empty selectors fail.
`--program=` must name an absolute executable path. The selector forwards every
argument after `--` unchanged, prefixes `native-build` or `run`, preserves the
working directory and exit status, and `exec`s the selected owner. It adds no
scheduler, timeout, resource budget, retry, cleanup, receipt or automatic
fallback. Use the existing bounded process owner around it. A nonzero owner
result remains nonzero. `--help` does not require a compiler.

For provisional bootstrap, retain immutable source, producer, runtime and tool
identities; private compatible caches; process-tree supervision; exact output
validation; and the new compiler's own compile/run Hello gate. Direct execution
does not mint a Phase2 admission receipt or qualify BuildRunner/TestRunner. The
high-level `bootstrap-from-scratch.sh` managed phase pipeline is unchanged;
`resume-stage3-from-admitted.sh` still requires genuine admission. A diagnostic
direct candidate remains unadmitted until its required gates pass. Do not put
it in `bin/release` or substitute it for an admitted producer.

Selector process contracts: `python3 scripts/build/tests/run-build-test.py`.
These tests use an argv-reporting process to check routing, precedence, exact
arguments, PID ownership, failures and rejection. They do not qualify native
BuildRunner execution. A real direct Cranelift Hello compile/run was also
checked with a pinned Phase2 compiler; this is selector integration evidence,
not completion of the bootstrap or map/AsyncRef qualification matrix.

## Essential applications after Stage 4

Every completed Stage 4 bootstrap must build and check DevHub, the Caret suite,
the hosted DB server, and the web server before recording acceptance or
performing deployment. Run `--full-bootstrap --full-cli` for the complete
bootstrap and required applications. The Stage 4 gates have no opt-out. Bare
`--full-bootstrap` retains its existing dynload phase boundary; explicit
`--stop-after-*` boundaries still stop at their requested phase.

After validating the full CLI and its basic tooling, the script produces the
Simple core archive, the core-C DB runtime capsule, and the host-GPU web runtime
capsule through their normal owners. It then runs
`scripts/check/check-bootstrap-essential-apps.shs` against that exact Stage 4
binary and provenance. Missing authorities, missing binaries, failed builds,
empty suites, or failed tests stop bootstrap. Runtime builds and application
checks retain separate logs under the bootstrap output directory.

The DB checks include SimpleDB SDN durability separately from the hosted
PostgreSQL-mimic executable. Application and GUI semantic tests do not establish
live window/input/capture acceptance; those results remain separately required
for GUI qualification.

## Reusing a Rust Cargo cache with a fresh output directory

On macOS and Linux, set `SIMPLE_BOOTSTRAP_RUST_CARGO_CACHE_ROOT` to an existing,
canonical cache parent directory in this Git worktree or a linked worktree of
the same repository. The selected target remains
`<cache-root>/rust-cargo-target-<computed-build-configuration-key>`; the caller
cannot supply or override that key. Windows keeps its existing short-path
cache layout and rejects this override.

Use a fresh `--output` directory for new logs and authority receipts while
retaining the existing cache parent. The script validates repository identity,
checks free space on the cache filesystem, and serializes canonical Cargo writers with
a lock in the common Git directory before taking the worktree's publication
lock. Cargo still decides which crates are fresh. Source fingerprints,
immutable generation publication, and admission checks remain required.
No cache copy, move, symlink, or forced producer stamp is involved.

## Stage 3 and the sanctioned script

- The sanctioned bootstrap is `scripts/bootstrap/bootstrap-from-scratch.sh`
  (see `.claude/rules/bootstrap.md`). `bin/simple build bootstrap` is a separate
  seed-side reimplementation, not this path.
- Stage 3 runs from a frozen, admitted Stage 2 (Stage 2 is ADMITTED on
  release/1.0.0, #4260). Do not edit or rebase the frozen tree
  ([frozen worktree](frozen_bootstrap_worktree.md)). A fix that lives in
  compiler source only takes effect after Stage 2 is rebuilt.
- #4498 (9965e560854): the whole-program bootstrap-fixed MIR lane in
  `driver_pipeline_lowering.spl` now prescans all closure structs
  (`prescan_module_struct_names`, mirroring the `--entry-closure` prescan). It
  cured 479 "array return record element has no unique provider layout" errors
  on the 1453-module closure. Needs a Stage 2 rebuild to take effect.
- #4499 (merged 2026-10-24): `module_source_relative_path` no longer cuts a
  repo-relative path at an inner `/src/`
  (`src/lib/nogc_sync_mut/src/collections/x.spl` was named `collections.x`).
  Absolute paths still anchor at the first `/src/`. All four naming callers
  (driver, backend, MIR, HIR) share the function.
- Windows link: `src/compiler_rust/runtime/build.rs` links `ws2_32` and
  `mswsock` (IOCP provider, #4430, merged). Windows default lane is llvm-mingw
  UCRT with clang + lld. Never GCC.

## Shard and memory knobs

Policy lives in `scripts/bootstrap/lib/product-frontend-policy.shs` and
`scripts/bootstrap/tests/phase-c-frontend-policy-test.shs`.

| Variable | Meaning / policy default |
|---|---|
| `SIMPLE_SHARD_MEM_CLAMP` | `1` (default); `0` is refused: "unbounded frontend fanout forbidden" |
| `SIMPLE_PARSE_SHARD_MAX` | Max parse-shard workers; the Windows owner pins `1` (one frontend) |
| `SIMPLE_PARSE_SHARD_WORKER_KB` | Per parse worker budget, policy value `1650000` |
| `SIMPLE_HIR_SHARD_WORKER_KB` | Per HIR worker budget, policy value `3000000` |
| `SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB` | Positive, enforced process-tree limit |
| `SIMPLE_HIR_SHARDING` / `SIMPLE_PARSE_SHARDING` | Switch HIR / parse sharding (`0` disables) |
| `SIMPLE_HIR_WORKER_SKELETON` | Opt-in (`=1`): HIR workers build surfaces from the module skeleton (#4473) |
| `SIMPLE_MIR_SHARDING` / `SIMPLE_FRONTEND_CACHE` | Stage 3 pass-throughs (unset \| `0` \| `1`, else refused) in `resume-stage3-from-admitted.sh` and `bootstrap-from-scratch.sh`; hashed into the args receipt and transcribed. Unset = pinned argv (sharding absent, frontend cache `1`) |

**Windows Stage 3 shard-worker AV workaround (W24/W27, 2026-11-23).** MIR shard
workers AV (`0xC0000005`, `claimed=0`) when they read back warm `.fpc`
frontend parse-cache entries. Run the canonical resume lane with
`SIMPLE_MIR_SHARDING=1 SIMPLE_FRONTEND_CACHE=0` exported: workers parse cold,
codegen, and exit per shard (verified 9/9 shards, 1612/1613 modules). This is a
scoped workaround; the `.fpc` read-back root cause is OPEN
(`doc/08_tracking/bug/stage3_surface_build_av_items_spl_warm_frontend_cache_2026-11-22.md`;
transport fix `stage3_resume_drops_mir_sharding_frontend_cache_env_2026-11-23.md`).
Stage 4 (full-CLI relink, release and debug-xray, including `--resume-stage4`)
honours the same caller `SIMPLE_FRONTEND_CACHE` (unset keeps the forced `1`;
`0`/`1` used; else refused), binds it into the Stage 4 cache context, the
build log (`stage4-frontend-cache:` line) and the provenance
(`stage4_frontend_cache=`, absent = `1`)
(`stage4_forces_frontend_cache_ignores_caller_2026-11-23.md`).

### Repo-tracked bootstrap settings (`config/bootstrap.sdn`)

Precedence for every key: CLI flag (where one exists) > env > config > built-in default.

| Key | Env override | Meaning |
|---|---|---|
| `jobs` | `--jobs`, `SIMPLE_NATIVE_BUILD_THREADS` | Build parallelism (`bootstrap-jobs.shs`) |
| `compiler`, `compiler_release` | `SIMPLE_BOOTSTRAP_COMPILER` | Next-phase compiler (`resolve-bootstrap-compiler.shs`) |
| `stage3_file_workers` | `SIMPLE_FILE_WORKERS` | Stage 3 route: `0` two-pass phase route (pinned, bug #8504), `1` per-file; absent = compiler default |

### Host settings (`config/host/<hostname>.sdn`, 2026-11-22)

Host-specific tuning lives in the host config, not in launcher env vars.
Precedence per knob: env var (or the CLI flag that sets it) > host config
(`sh scripts/setup/host-env.shs --get KEY`: `SIMPLE_HOST_<KEY>` > user
`~/.config/simple/host.sdn` > tracked `config/host/<hostname>.sdn`) >
`config/bootstrap.sdn` (file workers only) > built-in default. A host without
the key behaves exactly as before. The Stage 3 `env -i` child cannot read host
config, so the scripts resolve the key and export the env var
(`scripts/bootstrap/lib/host-bootstrap-settings.shs`).

| Host key | Exported as | Applied by |
|---|---|---|
| `mem_reserve_free_mib` | `SIMPLE_BUILD_MEMORY_RESERVE_BYTES` (MiB x 1048576) | `bootstrap-from-scratch.sh` startup, `resume-stage3-from-admitted.sh` |
| `stage3_tree_rss_cap_kib` | `SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB` | `resume-stage3-from-admitted.sh` (Stage 3 only) |
| `stage3_threads` | `SIMPLE_NATIVE_BUILD_THREADS` (coordinator route); skipped if either thread variable is set; `--jobs` wins. Direct fan-out (`SIMPLE_STAGE3_DIRECT_THREADS`>1) needs linux/darwin memory evidence and is not a host setting | `resume-stage3-from-admitted.sh` |
| `stage3_file_workers` (0/1) | `SIMPLE_FILE_WORKERS` lane item | `bootstrap_select_stage3_file_workers` (source `host-config`) |
| `frontend_cache` (`on`/`off`) | `SIMPLE_FRONTEND_CACHE` (`1`/`0`) for the Stage 2 verification matrix, Stage 3, and Stage 4 full-CLI relink; the Stage 2 producer build keeps its pinned `1` | `bootstrap-from-scratch.sh` startup (into the captured caller value, re-applied in the matrix subshell and used at the Stage 3 and Stage 4 launches), `resume-stage3-from-admitted.sh` (Stage 3 only) |
| `mir_sharding` (0/1) | `SIMPLE_MIR_SHARDING` | Stage 2 matrix subshell + Stage 3 launch in `bootstrap-from-scratch.sh`, `resume-stage3-from-admitted.sh` |
| `mir_shard_count` (1..128) | `SIMPLE_MIR_SHARD_COUNT` | same as `mir_sharding` (Stage 3 consumes it only on the per-file / interface-HIR lanes) |
| `mir_shard_worker_kib` | `SIMPLE_MIR_SHARD_WORKER_KB` | Stage 2 matrix only (kept over the whole-build two-worker floor); NOT forwarded across the Stage 3 `env -i` boundary |
| `sanity_build_timeout_seconds` (positive seconds) | `COMPILER_BUILD_TIMEOUT_SECONDS` (sanity-probe build cap, admission default 180) | `bootstrap-from-scratch.sh` startup and `resume-stage3-from-admitted.sh`, before each script's `:-180` default; explicit env wins, invalid = hard error |

The four matrix/shard keys (W27/W32/W36, 2026-11-23) apply only when their env
var is unset; an invalid value in any host-config layer is a hard error naming
the key, not a silent fall-through. They reach each matrix tool row through
`bootstrap_phase_c_tool_row_environment_keys` (`phase-c-backend-commands.shs`).
Bug: `doc/08_tracking/bug/host_config_matrix_shard_knobs_unreachable_2026-11-23.md`.

Note that a user `host.sdn` value beats the tracked per-host file; `--print`
shows which layer won. `sh scripts/setup/update-host-config.shs [--dry-run]
[--set KEY=VALUE]...` measures the host (CPUs -> `max_threads`; on Windows,
available RAM < 1/4 of total while process working sets hold < 1/2 is the
ballooned-guest pattern, #8931, and gives `mem_reserve_free_mib: 2048`) and
updates the per-host file in place. The `mir_*`/`frontend_cache` keys are
host-scoped workarounds for open defects (W27 warm `.fpc` read-back AV, W32
commit exhaustion); remove them from the per-host file once those are fixed.

Defaults fixed in code, not config (2026-11-13):

- **Stage 3 resume tree RSS cap.** With no
  `SIMPLE_BOOTSTRAP_COMPILER_RSS_CEILING_KIB` pair, the resume compiler's
  process-tree cap is the cgroup MemoryHigh the Stage 3 memory admission
  reserved (`SIMPLE_BOOTSTRAP_STAGE3_MEMORY_HIGH_MIB`, default = the 48 GiB
  headroom), clamped to the default hard ceiling
  (`bootstrap_tree_rss_stage3_default_cap_kib`, Linux). It used to fall to the
  8 GiB compile-worker budget, which killed every serial Stage 3 after HIR.
  The receipt records it as `source: memory-admission, bound: memory-high`
  (`hard-ceiling` when clamped): the worker publishes
  `SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_SOURCE/_BOUND` beside the transported
  cap, so a post-mortem never reads this code default as an operator
  `explicit-env` pair. `SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB` alone
  overrides it (attributed `explicit-env`), up to that ceiling. An elevated ceiling must exceed the default 48 GiB ceiling
  (strict ratchet), so a pair such as ceiling 32 GiB / cap 26 GiB is
  always refused.
- **Stage 3 resume go-to-end.** `SIMPLE_BOOTSTRAP_GO_TO_END` (default 1) now
  reaches the resume compiler as `SIMPLE_NATIVE_GO_TO_END` (per-file lane item
  `gte=`), like the in-script Stage 3. Before, the env -i worker dropped any
  ambient `SIMPLE_NATIVE_GO_TO_END`. `SIMPLE_COMPILE_FAIL_FAST` already
  defaults to off (`compile_failure_policy.spl`).
- `SIMPLE_CACHE_SCOPE` stays per-lane env identity, never config.

Stage 3 bisect (2026-10-25): turning skeleton and HIR sharding on or off did
not change the MIR error set, so they are not the cause of those errors.

## HIR cache self-check bug (OPEN)

Frozen-Stage-2 Stage 3 logs 313 `[hir-cache] SELFCHECK FAILED ...
nil_in_non_optional_scalar` lines; the encoder writes a nil token the generated
decoder refuses, so entries are not stored and HIR shard work is recomputed.
See `doc/08_tracking/bug/hir_cache_selfcheck_nil_in_non_optional_scalar_2026-10-25.md`.

## Standalone per-module / per-file lowering notes (#4525, historical 2026-10-25; Phase 3/4 scripts default to `--compile-mode=shard`)

Target design: `doc/05_design/compiler/incremental_build/src_based_tldr_build_v1.md`.
Landed pieces: FileFiber v1 per-file read + TLDR publish (#4453), single-flight
leaders (#4441), and #4525, which makes per-module lowering the standalone driver default
(while `scripts/bootstrap/build-phase3-phase4.sh` and `config/bootstrap.sdn` set `--compile-mode=shard` / `SIMPLE_FILE_WORKERS=0` by default and expose per-file workers via `--compile-mode=file`).

- `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1` is the only way into the whole-program
  bootstrap-fixed lane (one MirLowering over the closure, flat MIR passes
  skipped, single-object context dispatch). Unset: each module's MIR feeds the
  per-module witness-keyed object cache in `driver_aot_native_output.spl`, so
  `aot-<hash>.o` objects appear in the build dir one per module during codegen.
- #4525 is in compiler source, so it only applies once Stage 2 is rebuilt. With
  the frozen Stage 2 today, the per-file lane is reached by running the Stage 3
  native-build with `SIMPLE_BOOTSTRAP` and `SIMPLE_BOOTSTRAP_STAGE3` unset
  (entry `src/app/cli/bootstrap_main.spl`, `--entry-closure`, `--threads 80`).
- Measured 2026-10-25 (frozen Stage 2, 9-module closure, 8 threads): 9 objects,
  first at 160 s, last at 174 s, binary runs correctly.
- Under `SIMPLE_BOOTSTRAP=1` without `SIMPLE_BOOTSTRAP_STAGE3`, HIR sharding
  blocks with "HIR cache identity unavailable for shard", and the unsharded
  ambient-bootstrap HIR leaves cross-module imports unresolved. Use the unset
  lane above until those are fixed.
- Scripts (2026-10-25): `bootstrap-from-scratch.sh` Stage 3 and
  `resume-stage3-from-admitted.sh` (via `lib/stage3-native-build-worker.sh`,
  32-argument form, last positional `per-file`|`whole-program`) no longer
  force the shortcut. Default: the Stage 3 child gets `SIMPLE_BOOTSTRAP=`
  (empty) so the compiler takes the per-module lane. With
  `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1` exported it gets `SIMPLE_BOOTSTRAP=1
  SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1` (the old single-object lane). Both values
  are in the Stage 3 args hash, so the receipt records which lane ran; any
  other value of the knob is refused. The outer `export SIMPLE_BOOTSTRAP=1`
  is unchanged (Stage 3 runs under `env -i`). Stage 2 args and their resume
  reconstruction are untouched.
- Objects, cache, link: each module's object is `aot-<hash>.o`, keyed by the
  module witness in the per-module object cache under
  `SIMPLE_NATIVE_BUILD_CACHE_DIR/<producer scope>/` (index `build_cache.sdn`;
  Stage 3 points it at `stage3/<triple>/stage3-native-cache`); an
  unchanged module is a cache hit and is not re-emitted. Codegen fans out over
  `SIMPLE_NATIVE_BUILD_THREADS`, which the scripts set to `selfhost_jobs`
  (`bootstrap-build-jobs-policy.shs`: `--jobs` > `SIMPLE_BOOTSTRAP_MAX_BUILD_JOBS`
  > `~/.config/simple/host.sdn` `max_build_jobs` > 16). All objects plus the
  runtime bundle are then linked into one binary.
- Not yet proven: a full Stage 3 run of the per-file lane under
  `SIMPLE_BOOTSTRAP_STAGE3=1` with `SIMPLE_BOOTSTRAP` empty. If it fails, use
  `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1` and record the failure.
- Per-file pipeline default (P-F): the default
  for `SIMPLE_FILE_WORKERS` when unset is the
  single constant `NATIVE_PER_FILE_PIPELINE_DEFAULT_V1` in
  `src/compiler/80.driver/driver_build/native_file_worker_v1.spl` (now
  `"1"`). Unset or `SIMPLE_FILE_WORKERS=1` selects the per-file `src → obj` pool;
  `SIMPLE_FILE_WORKERS=0` opts out, and
  `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1` keeps the whole-program route. The Stage 3
  scripts pass the knob through when set (exactly `0` or `1`, anything else
  is refused) and hash it into the Stage 3 args receipt; unset adds nothing,
  so existing receipts stay resume-compatible. The resume worker receives it
  as a lane suffix (`per-file:fw=0|1`) because systemd does not inherit
  the caller's env. Jobs still come from `~/.config/simple/host.sdn`
  `max_build_jobs`. Overlap proof:
  `sh scripts/check/check-per-file-overlap-receipt.shs <receipt dir>...`
  (`--selftest` first, always) passes only when some `obj_done(A) <
  hir_start(B)` and reports `first_object_ms` and `objects_per_min`.
- Known WA: `WA-PERFILE-TRIPLE-QUOTE`
  (`doc/08_tracking/bug/perfile_lane_triple_quote_interpolation_parse_2026-10-25.md`).

## Cache protocol (all landed 2026-10-24)

- `.spab` packed pointer-free AST: encoder + validating reader (#4445), hit path
  via mmap view and typed-token restore (#4457), reference table 0x0104 and
  set-once map 0x0900 (#4463). Opt-in with `SIMPLE_FRONTEND_SPAB=1`; the default
  flips only after the whole-closure native gate passes on a Stage 3 binary.
  Design: `packed_binary_ast_v1.md`.
- `DigestV1 { algo_id, hex }` over a hash algorithm registry (#4421):
  `sha256`=1, `blake3`=2, `sha3-256`=3 (collision-resistant); `xxh3-128`,
  `xxh3-64`, `crc32` (fast fingerprints). Up to 3 digests per side are
  negotiated; an unknown algorithm or length mismatch is a MISS, never a match,
  and different algorithms never compare. Macro keys (#4435), generic
  identities (#4433) and persisted build-cache digests (#4481) use it.
- `GuardIdV1` + `ActiveGuardRootV1` (#4412, #4420): guard root is part of the
  AOP directory key.
- Single-flight: leaders get a start time and always complete (#4441).
- Daemon file-queue request loop and usage ledger (#4396); per-source disk and
  memory byte caps (#4405); free-space admission before every publish (#4442);
  reference-aware eviction (#4458).
- Lean formal gate (#4411): `scripts/check/check-cache-protocol-formal.shs` and
  `scripts/check/check-cache-formal-source-binding.shs` (pins sha256 of live
  cache-key declarations; re-pin with `--update` after review). Missing `lake`
  is ERROR exit 2, never PASS. Theorems landed: T-K1/T-I1 (#4415), T-RR1
  (#4447), T-RG1 (#4449), T-EV1 (#4451), T-HA1 (#4452), T-SF1 (#4427).

## Process

- Never `git stash` (shared across worktrees); use your own `work/*` worktree.
- Merge a PR only when `gh pr checks <n> | grep '^Code Idiom'` is green.
- Take host job counts from `~/.config/simple/host.sdn`.
- Never GCC on Windows.

## Stage3 entry admission requirements

`native-build` (stage3 entry) admits sources through the SCV source authority and
refuses with `SCV-E-ADMISSION`. Three requirements are easy to miss; the refusal
now prints a `SCV-E-ADMISSION: hint:` line naming the one that failed
(`native_build_admission_hint_v1`, `src/app/cli/native_build_main.spl`):

1. **Root must be a git work tree.** Inventory events come from git; without
   `.git` the refusal is `git-event-source-unavailable`. Run from inside a git
   checkout.
2. **Entry must live under the checkout root in a known family** (`test/`,
   `src/`, or `examples/10_tooling/`). Other existing in-root paths are only
   auto-admitted when they are real files/directories; outside the root is
   refused as `source-inventory-scope-unsupported`.
3. **One `--source` per path.** `--source a,b` or `--source "a b"` is a single
   (nonexistent) path; write `--source a --source b`.


## Stage-3 admission runbook

Moved from `stage3_hard_blocked_on_stage2_admission_2026-08-31` (closed 2026-11-09). Measured 2026-08-31 on aarch64-apple-darwin; line numbers are as of that date.

Status: BLOCKED — not a defect in the Stage-3 lane. Investigation + pre-staged runbook.

### 1. Stage-3 entry contract (both lanes)

### Lane A — `--stop-after-stage3`
`scripts/bootstrap/bootstrap-from-scratch.sh:386-393` — excludes resume/full-cli/
deploy/release/diagnostic and requires `--mode=dynload`.
`:409-424` — the trust-root receipt exception is granted **only** to
`--stop-after-stage2 --full-bootstrap`. Every other path, `--stop-after-stage3`
included, falls to the `elif` at `:417` and exits **64** with
`bootstrap-policy-error: reason-receipt-required`.
`:432-437` — receipt `target` must be exactly `//bootstrap:stage3`.
`:438-441` — `bootstrap_planner_v2_verify <receipt> <root>` must pass.

### Lane B — `--resume-stage3-from-admitted=<output>`
`bootstrap-from-scratch.sh:501-510`: mutually exclusive with rebuild/deploy/
diagnostics, `--jobs=1` only, then `exec resume-stage3-from-admitted.sh`.
That script (`:25-31`) re-verifies the same v2 receipt and re-checks
`target == //bootstrap:stage3`, then at `:178-194` requires ALL of these to exist
as canonical non-symlink files under `<output>/stage3/<platform>/`:

    stage2 = <output>/stage2/<platform>/simple
    admitted = stage3/<platform>/stage2-admitted/simple
    stage2_admission = stage3/<platform>/stage2-admitted/admission.env
    seed, stamp (simple.inputs.sha256), libsimple_native_all.a
      under stage3/<platform>/stage2-runtime-authority/
    stage2-sanity.env, stage2-receiver.env, stage2-receiver.log,
    stage2-command.transcript, logs/<platform>/stage2-native-build.log,
    source-inputs-before.txt, git-state-before.env,
    runtime-origin-{before,after}.txt, runtime-admitted.txt,
    tool-authority-before.txt
    + dirs: stage2-runtime-authority/, stage2-native-cache/

### 2. How a receipt is legitimately produced

You do **not** hand-compute the four sha256 values, and you do **not** run
`bootstrap_receipt_main.spl` yourself. The error message at `:417` quotes the
*inner* command the producer execs. The real producer is:

    sh scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs \
      --target='//bootstrap:stage3' \
      --reason=verify-landed-compiler-fix \
      --parent-compiler=build/bootstrap/stage2/aarch64-apple-darwin/simple

Where each digest comes from (`produce-bootstrap-planner-admission-v2.shs`):
- `parent_compiler_sha256` — `:150` sha256 of the Stage-2 binary itself.
- `runtime_snapshot_sha256` — `:165-169` sha256 of a sorted
  `find src/runtime -type f ! -path './vendor/*' | sha256sum` manifest.
- `planner_source_closure_sha256` — `:173-179` sha256 of a snapshot holding the
  planner source hash + its `extern fn` lines (the planner imports no modules).
- `planner_sha256` — `:213` sha256 of the planner binary built **by the Stage-2
  parent** via `native-build --entry-closure --entry src/app/cli/bootstrap_reason_planner.spl`.
- `cache_scope_key` = `sha256("<runtime_sha>:<closure_sha>")` (`:187`), and it
  names the admission directory — verified independently at
  `bootstrap-planner-admission-bound.shs` verify_structure.

Note the planner SOURCE is `src/app/cli/bootstrap_reason_planner.spl`
(pinned literally in `verify_structure`), not `bootstrap_receipt_main.spl`.
Allowed `//bootstrap:stage3` reasons: `bootstrap_planner_v2_reason_allowed`,
`bootstrap-planner-admission-bound.shs` — `seed-missing`, `seed-corrupt`,
`seed-target-unsupported`, `seed-cannot-parse-required-language-feature`,
`seed-cannot-lower-required-compiler-feature`, `bootstrap-runtime-abi-major-changed`,
`bootstrap-artifact-format-major-changed`, `bootstrap-core-interface-major-changed`,
`verify-landed-compiler-fix`.

### 3. Why Stage 3 can make ZERO progress today — hard prerequisite

Stage-2 admission failed and the binary was renamed
(`bootstrap-from-scratch.sh:2428`, `stage2-rejected/`):

    build/bootstrap/stage2/aarch64-apple-darwin/simple           MISSING
    build/bootstrap/stage2/aarch64-apple-darwin/simple.rejected  sha 9050d3a8c1e387d54a5975a517637392b02f1cc1435ff7c1a44ffadaf7c1e7b8 (Aug 31 06:28)
    build/bootstrap/stage3/aarch64-apple-darwin/stage2-admitted/ DOES NOT EXIST

Blocking cause (`stage3/aarch64-apple-darwin/stage2-receiver.env`, status=fail,
probe_exit=1; log tail):

    error: bootstrap MIR lowering: E-MIR-TYPE-Unknown: unreachable HirTypeKind
    disc=-1: 0 while lowering
    'compiler.common.module_path_naming._module_path_naming_text_index_of'

### Proof A — the stale Aug-24 receipt no longer verifies
    sh scripts/bootstrap/bootstrap-from-scratch.sh --validate-bootstrap-receipt \
      --stop-after-stage3 --bootstrap-receipt=build/bootstrap/stage3-admission.env \
      --backend=llvm
    -> bootstrap-policy-error: planner-admission-v2-unbound
       bootstrap-policy-error: malformed-or-untrusted-planner-admission-v2   exit 64

Why: `verify_structure` loops over ten `<stem>_path` fields and calls
`bootstrap_planner_v2_canonical_file` + re-hash on each. The receipt's
`parent_compiler_path=.../stage2/aarch64-apple-darwin/simple` no longer exists,
and its recorded `parent_compiler_sha256=8cc20c89…` does not match anything on
disk. There is also `bootstrap_planner_v2_verify_parent_compiler_binding`, which
requires receipt-sha == produced-sha == consumed-sha at consumption time.

### Proof B — a fresh receipt cannot be minted
    sh scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs \
      --target='//bootstrap:stage3' --reason=verify-landed-compiler-fix \
      --parent-compiler=build/bootstrap/stage2/aarch64-apple-darwin/simple
    -> bootstrap-admission-error: parent-compiler-missing-or-not-canonical   exit 64

The producer's step 2 (`:97-142`) refuses any parent that is not under
`<output>/stage2/`, that lacks a passing `stage2-sanity.receipt` +
`stage2-provenance.receipt`, or whose sha does not equal both receipts'
`candidate_sha256`. This runs BEFORE the admission lock, so the failed attempt
left no side effects.

**Conclusion:** admission is a hard prerequisite, not a soft one. Stage 3 needs an
*admitted* Stage-2 binary in two independent places — the receipt chain
(producer step 2 + `verify_parent_compiler_binding`) and the resume lane's
required-inputs loop (`resume-stage3-from-admitted.sh:178-194`, which demands
`stage2-admitted/simple` and `stage2-admitted/admission.env`). No legitimate
receipt exists or can be produced until the `E-MIR-TYPE-Unknown` defect is fixed
and a Stage-2 run admits.

Not attempted, deliberately: restoring a stale binary into
`stage2/aarch64-apple-darwin/simple`. No byte-identical admitted copy of
`8cc20c89…` survives anywhere (`stage2-admitted/` is gone), so this would be
fabrication, not recovery.

### 4. Pre-staged runbook — run in order the moment Stage 2 admits

    # 0. no concurrent bootstrap
    pgrep -f bootstrap-from-scratch   # must print nothing

    # 1. preconditions: admitted parent present, shas agree
    P=build/bootstrap/stage2/aarch64-apple-darwin
    shasum -a 256 "$P/simple"
    grep candidate_sha256 "$P/stage2-sanity.receipt" "$P/stage2-provenance.receipt"
    # all three hex values must be identical, and
    #   'stage2-sanity: pass' + 'stage2-provenance: pure-simple' must be present

    # 2. mint the receipt (derives all four sha256s itself)
    sh scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs \
      --target='//bootstrap:stage3' \
      --reason=verify-landed-compiler-fix \
      --parent-compiler="$P/simple"
    # last stdout line: 'bootstrap-admission: produced <receipt>'  exit 0

    # 3. validate without executing (cheap, safe)
    sh scripts/bootstrap/bootstrap-from-scratch.sh --validate-bootstrap-receipt \
      --stop-after-stage3 --bootstrap-receipt=<receipt> --backend=llvm
    # 'bootstrap-policy: receipt-valid target=//bootstrap:stage3 ...' exit 0

    # 4a. Lane A — fresh Stage 3
    sh scripts/bootstrap/bootstrap-from-scratch.sh --stop-after-stage3 \
      --mode=dynload --backend=llvm --bootstrap-receipt=<receipt>

    # 4b. Lane B — resume from an admitted Stage 2 (only if stage2-admitted/ exists)
    sh scripts/bootstrap/bootstrap-from-scratch.sh \
      --resume-stage3-from-admitted=build/bootstrap \
      --bootstrap-receipt=<receipt> --jobs=1 --backend=llvm
    # Pass --bootstrap-receipt, NOT SIMPLE_BOOTSTRAP_REASON_RECEIPT. The receipt
    # gate at bootstrap-from-scratch.sh:417 tests the FLAG variable and fires
    # 'reason-receipt-required' (exit 64) long before the exec at :510. The
    # script exports SIMPLE_BOOTSTRAP_REASON_RECEIPT itself (:444-445) only
    # after the receipt verifies, which is what resume-stage3-from-admitted.sh
    # then reads at :24-31. Setting that env var by hand is both insufficient
    # (the flag gate still refuses) and unnecessary.

### 5. Where the real diagnostic lives when Stage 3 says UNDIAGNOSABLE

    build/bootstrap/stage3/aarch64-apple-darwin/stage2-receiver.log   (Stage-2 probe)
    build/bootstrap/stage3/aarch64-apple-darwin/stage3-sanity.env
    build/bootstrap/stage3/aarch64-apple-darwin/stage3-native-build-status.env
    build/bootstrap/logs/aarch64-apple-darwin/stage3-native-build.log

`resume-stage3-from-admitted.sh:78-130`
(`bootstrap_stage3_resume_effective_status`) classifies a shell-status-0 run
that hides a crashed worker by grepping the log for
`^error: native-build worker exited with code ` — worker status `4294967295`
means signal-or-wait-failure, NOT SIGSEGV.

### RESOLVED 2026-08-31 — Stage 2 ADMITTED

The bootstrap now exits `rc=0` with "Stage 2 admitted; stopping before Stage 3 as
requested." Verified N=10: `rc=0` 10/10, `lines=12` (non-vacuous) 10/10,
`bootstrap_stage2_struct_receiver=PASS` 10/10.

Nine defects were fixed to get here: seed positional entry; 3x Stage-2 SIGSEGV
chains; `rt_heap_ref_wellformed` lost to a stale-snapshot clobber; `(24<<32)`
LocalId corruption from an un-unwrapped `LocalId?`; cross-file trait no-op
shadowing; MC/DC probes emitted with no runtime backing; text `+` merged as an
array; the stolen `unwrap` making every call-result return emit `ret 0`; and
`print` not newline-terminating.

Stage 3 is no longer blocked by admission. It requires its own planner-admission-v2
receipt with typed reason `verify-landed-compiler-fix` (target `//bootstrap:stage3`),
produced by `scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs`.
Stage 4 needs a DIFFERENT reason -- one of `self-host-convergence-check`,
`release-trust-verification`, `diverse-double-compilation`.
