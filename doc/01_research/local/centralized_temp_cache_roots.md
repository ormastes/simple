<!-- codex-research -->
# Centralized Temporary and Cache Roots — Local Repository Research

**Status:** local research only; no implementation or final requirement selection  
**Date:** 2026-09-03  
**Repository base:** `60de2dfcf51`  
**Feature:** `centralized_temp_cache_roots`

## 1. Research question

The repository currently creates temporary files, caches, generated build state, and agent worktrees under many unrelated roots. This research inventories the production and major script owners and evaluates a strict two-root model:

1. one user-scoped storage root outside every source worktree;
2. one current-worktree storage root inside the active worktree.

Every Simple-owned temporary or cache directory would be a structured descendant of exactly one of those roots. OS and third-party tools may still use their native temporary/cache roots internally when Simple does not control their path.

## 2. Method and observed scale

The inventory searched `src/`, `scripts/`, `bin/`, `config/`, `.github/`, `test/`, and `doc/`, excluding Git metadata, generated `build/` contents, and owned-code exclusions under `src/compiler_rust/vendor/**` and `src/runtime/vendor/**`.

The repository has broad path-policy scatter:

| Literal or concept | Files containing it | Interpretation |
|---|---:|---|
| `/tmp` | 4,344 | Mostly tests/history, but many production scripts and several runtime/compiler paths hard-code it. |
| `TMPDIR` | 625 | Dominant portable temporary override, usually with `/tmp` fallback. |
| `mktemp` | 1,154 | Strong script convention, but naming, cleanup, and root selection are decentralized. |
| `.cache` | 812 | Mix of user caches, language caches, documentation, and fixtures. |
| `cache-dir` | 281 | CLI/tool-specific configuration, not one repository-wide policy. |
| `build/tmp` | 180 | Worktree-local scratch convention, but not authoritative. |
| `git worktree` | 131 | Worktree creation/removal is spread across release, check, migration, and agent flows. |

These counts are discovery indicators rather than migration counts: documentation and generated manuals account for many hits, and tests intentionally construct foreign layouts. A migration must classify owners instead of mechanically replacing strings.

## 3. Existing authorities

### 3.1 Compiler host-shared cache

`src/compiler/80.driver/cache/cache_root.spl` is the strongest existing centralized policy:

- `host_cache_base()` honors `SIMPLE_HOST_CACHE_ROOT`, then `XDG_CACHE_HOME`, then `$HOME/.cache/simple`, finally `/tmp/simple-cache`;
- `machine_cache_root()` honors exact `SIMPLE_CACHE`, otherwise uses a versioned project namespace;
- comments correctly require machine-tier immutable content to live outside worktrees so concurrent worktrees can share it.

`scripts/bootstrap/lib/host-shared-cache.shs` duplicates that resolution for bootstrap scripts and exports `SIMPLE_CACHE`. It intentionally leaves mutable native caches lane-private.

This is a good semantic split, but not a complete root policy. It is Linux-shaped on macOS (`$HOME/.cache`) and its `/tmp` fallback turns durable cache state into OS-temporary state when `HOME` is absent.

### 3.2 Package caches

There are at least three package-cache conventions:

- `src/lib/{nogc_sync_mut,nogc_async_mut,gc_async_mut}/package/paths.spl` uses `$HOME/.cache/simple` or `/var/cache/simple` for system mode;
- `src/app/cache/main.spl` manages `$HOME/.simple/cache`;
- `src/app/package/registry/config.spl` and `src/app/package.registry/config.spl` use two parallel registry implementations, one containing a literal `~/.simple/cache/registry`, the other an expanded `$HOME/.simple/cache/registry`.

The CLI's `simple cache clean` therefore does not necessarily clean the compiler machine cache or all package-family caches. Naming one directory “the cache” currently overstates its authority.

### 3.3 Compiler/runtime scratch and caches

`src/compiler/70.backend/backend/runtime_compiler.spl` has a private `_get_temp_dir()` implementing `TMPDIR -> TMP -> TEMP -> platform fallback`. It places compile probes and per-process runtime objects directly below that root. Its runtime-object cache defaults to `<temp>/simple-rt-objcache`, even though it is content-addressed reusable state. This couples reusable cache lifetime to OS temporary cleanup and mixes cache and scratch in one namespace.

`src/compiler/70.backend/linker/mold.spl` has another private `create_temp_dir()`:

- Windows uses `TMP`, then `TEMP`, then `C:/Windows/Temp`;
- POSIX hard-codes `mktemp -d /tmp/simple_link_XXXXXX`, ignoring `TMPDIR`;
- cleanup authorizes deletion by checking whether the path contains `simple_link_`, rather than proving containment beneath an owned root.

`src/compiler/80.driver/driver_aot_native_output.spl`, `driver_aot_smf_output.spl`, `driver_pipeline_lowering.spl`, and the modules under `src/compiler/80.driver/cache/` already consume `machine_cache_root()`. This makes the driver cache a viable first adopter of a common resolver rather than a new independent cache system.

### 3.4 MCP and tool-server paths

`config/mcp/mcp_startup_lib.shs` has three different policies in one startup path:

- debug logs default to `/tmp/<server>_debug_<cwd>`;
- native-health state defaults to `/tmp/<server>_native_health_<cwd>.state`;
- compiled SMF caches live under `<repo>/.simple/cache/<server>`;
- compile capture uses `mktemp "${TMPDIR:-/tmp}/..."`;
- persistent logs live under `<repo>/.simple/logs`.

The cwd-derived `/tmp` names are collision-prone after sanitization, leak across worktrees with similar paths, and are difficult to clean without broad globbing. The compiled cache is correctly worktree-sensitive in practice, but it lacks a declared root contract.

`bin/devhub`, `scripts/setup/setup.shs`, and release/check wrappers repeat the `${TMPDIR:-/tmp}` convention. They should consume a shell resolver, not each reproduce fallback policy.

### 3.5 Process and application state

`src/app/process/registry.spl` stores process-gateway state under `$HOME/.simple/cache/process_gateway.sdn`. This is mutable registry/state, not a recomputable cache. The new hierarchy must distinguish `state/` from `cache/`; otherwise cache cleanup can destroy ownership records.

`src/lib/nogc_sync_mut/ui/access_store.spl`, package registry code, and other app services also use user-home paths directly. They need classification before migration: credentials and durable user state are not temporary/cache data and must not be swept into this feature merely because they share `.simple`.

### 3.6 Bootstrap isolation

`scripts/bootstrap/bootstrap-phase-verification.shs` is a positive model. It derives private `home`, `tmp`, `cache`, work, and output descendants from one run root and invokes phases with explicit `HOME`, `TMPDIR`, and cache arguments. `scripts/bootstrap/stage4-tooling-matrix.shs` similarly creates task-specific homes and temporary roots.

`scripts/bootstrap/bootstrap-build-jobs-policy.shs` explicitly requires distinct HOME/TMP/cache/result roots. These flows show why structured descendants are necessary for concurrency and reproducibility, but each script currently invents its own hierarchy.

Bootstrap authority/provenance paths must remain distinct from disposable scratch. Producer receipts and admitted archives cannot be moved under a cleanup-prone `tmp/` subtree.

### 3.7 Worktree creation and cleanup

`scripts/release/converge-reviewed-fix.shs` defaults linked worktrees to a sibling `.worktrees` directory outside the coordinator worktree. It validates that the root is absolute, not a symlink, not inside the coordinator worktree, not inside Git administrative data, and not nested within another registered worktree. This is the best current safety policy.

Other creators include:

- `scripts/scv-migration/push-both.shs`;
- `scripts/check/check-main-test-runnable-push.shs`;
- `scripts/check/check-seed-builds-push.shs`;
- `scripts/check/check-build-outcome-reason-attribution.shs`;
- `scripts/check/check-core-bare-sanity.shs`;
- agent/session code exercised by `test/01_unit/app/llm_caret/agent_workspace_spec.spl`.

Observed live development also uses `/private/tmp/simple-*`, `/tmp/simple-*`, repository siblings, and tool-specific scratch roots. Git knows about linked worktrees but cannot remove abandoned non-worktree artifacts around them. A single user-root `worktrees/` namespace would make enumeration and age/lease cleanup possible.

### 3.8 Cleanup conventions

Most shell checks use `mktemp -d` plus a trap, which is locally safe when the trap runs. Risks remain:

- SIGKILL, machine reboot, or parent termination leaves trees behind;
- cleanup often authorizes `rm -rf` by a filename prefix rather than canonical containment;
- some scripts use predictable `$$` names instead of atomic creation;
- multiple cleanup commands call `git worktree remove --force` and `git worktree prune` independently;
- caches and temporary artifacts sometimes share a parent, making age-based cleanup unsafe;
- tests may intentionally override `TMPDIR=.` and produce ignored root-level residue;
- no common lease/owner receipt distinguishes active from abandoned agent worktrees.

`.gitignore` ignores `build/`, `.simple/`, `tmp/`, `temp/`, `.tmp*/`, and `.claude/worktrees/`, confirming multiple accepted worktree-local locations rather than one canonical location.

## 4. Other language and tool policies observed on this host

These are useful interoperability constraints, not proposed Simple authorities:

| Tool | Temporary policy | Cache/build policy | Lesson for Simple |
|---|---|---|---|
| Go 1.27.1 | `GOTMPDIR` is unset, so Go uses the OS temporary service. | `GOCACHE=/Users/ormastes/Library/Caches/go-build`; modules use `$GOPATH/pkg/mod`. | Temporary and reusable caches are distinct; macOS cache defaults follow platform conventions. |
| Rust/Cargo 1.94 | Rust compiler temporary files use platform/process facilities unless directed by the invoking build. | `CARGO_TARGET_DIR` is unset, so target output is worktree/package-local; shared downloads/toolchains use Cargo home. | Build products are project-scoped while downloaded/shared material is user-scoped. |
| npm | Uses `/Users/ormastes/.npm`. | User-scoped shared cache independent of a worktree. | External tool caches should be redirected only through supported variables, not moved after creation. |
| Python 3.14 | `tempfile.gettempdir()` resolves to the macOS per-user `/var/folders/.../T` directory. | Bytecode/environment caches are separate and context-specific. | Do not replace secure platform temp creation for unmanaged libraries; set their environment at process launch when isolation is required. |

The host itself has `TMPDIR=/var/folders/.../T/`, but Simple code frequently falls back or hard-codes `/tmp`, bypassing the user-scoped macOS temporary namespace.

## 5. Proposed exact two-root model

### 5.1 Canonical environment contract

Use exactly two Simple-owned root variables:

```text
SIMPLE_USER_STORAGE_ROOT
SIMPLE_WORKTREE_STORAGE_ROOT
```

Definitions:

- `SIMPLE_USER_STORAGE_ROOT` is the only root for cross-worktree, user-owned, reusable or session-managed material.
- `SIMPLE_WORKTREE_STORAGE_ROOT` is the only root for material whose identity or safe reuse depends on the current source worktree/revision/configuration.

The variables name Simple storage authorities, not replacements for standard `HOME`, `TMPDIR`, `XDG_CACHE_HOME`, `GOCACHE`, `CARGO_TARGET_DIR`, or npm configuration. Child processes receive those standard variables projected from the selected Simple subtree when isolation is required.

Recommended defaults:

| Platform | User root default | Worktree root default |
|---|---|---|
| macOS | `$HOME/Library/Caches/simple` | `<worktree>/.simple` |
| Linux/Unix | `${XDG_CACHE_HOME:-$HOME/.cache}/simple` | `<worktree>/.simple` |
| Windows | `%LOCALAPPDATA%/Simple` | `<worktree>/.simple` |
| no home/cache service | fail for durable/shared cache; use an explicitly supplied root | `<worktree>/.simple` when writable |

Do not silently fall back to global `/tmp/simple-cache` for reusable authenticated cache data. A caller needing hermetic operation must set both roots explicitly.

### 5.2 Structured user root

```text
${SIMPLE_USER_STORAGE_ROOT}/
  cache/
    compiler-cas/v1/projects/<project-id>/
    runtime-objects/v1/<toolchain-id>/<input-digest>/
    packages/v1/
    registry/v1/
    tools/<tool>/<version-or-digest>/
  tmp/
    processes/<pid>-<nonce>/
    sessions/<session-id>/
    downloads/<nonce>/
  worktrees/
    <repository-id>/<session-id>-<lane>-<revision>/
  state/
    leases/
    process-gateway/
    health/
  logs/
    sessions/<session-id>/
```

`cache/` is recomputable and GC-managed. `tmp/` is disposable and lease/age managed. `worktrees/` is removed only through Git-aware cleanup. `state/` is mutable authority and is never deleted by cache cleanup. `logs/` has an explicit retention policy.

### 5.3 Structured current-worktree root

```text
${SIMPLE_WORKTREE_STORAGE_ROOT}/
  cache/
    compiler-local/v1/
    mcp/<server>/
    indexes/
    native/
  tmp/
    compiler/<run-id>/
    linker/<run-id>/
    tests/<suite>/<run-id>/
    tools/<tool>/<run-id>/
  build/
    <target>/<profile>/
  evidence/
    <feature-or-gate>/<run-id>/
  logs/
    <product>/<run-id>/
  state/
    workspace/
    health/
```

The source tree contains only the single ignored `.simple/` root. Existing top-level `build/` remains a compatibility projection during migration; new APIs should treat `${SIMPLE_WORKTREE_STORAGE_ROOT}/build` as authoritative. Evidence intended for source control must still be deliberately promoted into `doc/` and must never be cleaned as ephemeral worktree state.

### 5.4 Placement decision

| Data class | Root | Reason |
|---|---|---|
| Content-addressed compiler artifacts reusable across worktrees | user `cache/` | Identity is digest/project based, not path based. |
| Runtime C object memo keyed by toolchain and content | user `cache/` | Current placement under OS temp loses valuable reuse. |
| Package downloads and registry indexes | user `cache/` | Shared, reproducible inputs. |
| Agent linked worktrees | user `worktrees/` | Must be outside source worktrees and centrally enumerable. |
| Agent/process leases and process registry | user `state/` | Mutable authority, not disposable cache. |
| One command's transient files | selected root `tmp/` | User root for cross-worktree agents; worktree root for source-bound commands. |
| Native output and source-revision indexes | worktree `build/` or `cache/` | Reuse depends on worktree/config identity. |
| MCP compiled service image | worktree `cache/mcp/` unless digest-global | Avoid cross-revision semantic drift. |
| Test scratch | worktree `tmp/tests/` by default | Easy local cleanup and attribution. |
| Release/bootstrap admitted artifacts and receipts | worktree `evidence/` or explicit output root | Must survive temp/cache cleanup and preserve provenance. |

## 6. Resolver ownership and API shape

One low-level environment/path owner should resolve both roots. Production modules and scripts must not independently read `TMPDIR`, `TMP`, `TEMP`, `HOME`, `XDG_CACHE_HOME`, or platform cache variables after migration.

Suggested logical operations:

```text
user_storage_root()
worktree_storage_root()
user_cache_path(owner, schema_version, key)
user_temp_session(owner, session_id)
user_worktree_path(repository_id, session_id, lane, revision)
worktree_cache_path(owner, schema_version, key)
worktree_temp_session(owner, run_id)
worktree_build_path(target, profile)
worktree_evidence_path(owner, run_id)
```

Shell scripts need one sourced counterpart that exports derived paths and standard child-process projections. The Simple implementation and shell implementation require shared fixtures so they cannot drift as `cache_root.spl` and `host-shared-cache.shs` currently can.

All path segments must be canonicalized or digest-derived. Cleanup APIs must receive an owned handle/receipt or prove canonical containment beneath the expected class root; substring/prefix-only deletion authorization is insufficient.

## 7. Compatibility and migration order

### 7.1 Environment precedence during transition

Recommended precedence:

1. exact legacy leaf override, when the owning subsystem already documents one (`SIMPLE_CACHE`, `SIMPLE_RT_OBJ_CACHE_DIR`, explicit `--cache-root`, explicit `--worktree-root`);
2. new root plus structured descendant;
3. legacy platform-derived default only in a compatibility phase, with a warning/receipt;
4. fail closed when durable authority would otherwise fall back to anonymous global temporary storage.

Legacy variables remain leaf overrides, not additional roots. For example, `SIMPLE_CACHE` may point directly at the compiler CAS while `SIMPLE_USER_STORAGE_ROOT` owns all other shared classes.

### 7.2 Migration waves

1. Introduce root-resolution contracts and cross-platform fixtures without moving data.
2. Move compiler machine cache and bootstrap shell projection behind the common resolver.
3. Move runtime-object cache from OS temp into user `cache/runtime-objects/`.
4. Move compiler/linker probes and scratch into structured `tmp/` sessions.
5. Move MCP caches, health state, debug logs, and compile scratch into typed worktree/user subtrees.
6. Centralize agent/release/check worktree creation under user `worktrees/` with leases.
7. Migrate package cache commands and resolve the `$HOME/.cache/simple` versus `$HOME/.simple/cache` split.
8. Migrate major test/check scripts mechanically only after owner-specific exceptions and cleanup semantics are recorded.
9. Add a ratchet rejecting new direct `/tmp`, `${TMPDIR:-/tmp}`, private temp resolvers, and new top-level cache roots outside approved adapters/fixtures.
10. After a compatibility window, remove legacy discovery and provide an explicit one-time migration/cleanup command.

## 8. Major migration risks

### 8.1 Cache correctness and poisoning

Moving caches can accidentally broaden reuse across worktrees. Every user-shared cache key must include the relevant repository/project namespace, schema version, compiler/provider/toolchain identity, target, flags, and source/input digest. Path relocation alone does not make a cache safe to share.

### 8.2 Bootstrap provenance

Authenticated stage archives, producer receipts, and promotion evidence must not be classified as cache or temp. Cleanup or cross-worktree reuse without exact authority tuples would invalidate bootstrap evidence.

### 8.3 Worktree nesting and Git administration

The user worktree root must remain outside every registered worktree and Git common directory. Preserve the canonicalization and anti-symlink checks in `converge-reviewed-fix.shs`. A root variable must not weaken those checks.

### 8.4 Concurrent cleanup

Age-only cleanup can delete active compiler, test, worker, or agent sessions. User-root `tmp/` and `worktrees/` require atomic leases containing owner PID/process start identity, session ID, creation/heartbeat time, repository ID, and cleanup class. Stale PID reuse must not count as a valid lease.

### 8.5 Security and symlinks

Central roots increase deletion blast radius. Creation and cleanup must reject symlink roots, `..` traversal, empty/root paths, cross-device surprises where atomic publication is required, and descendants that resolve outside their admitted root.

### 8.6 Cross-platform semantics

macOS should use `~/Library/Caches`, Linux should honor XDG, and Windows should use LocalAppData. Case folding, path length, drive letters, UNC paths, and filesystem permissions require generated fixtures. Hard-coding Unix separators or assuming `$HOME` is always present would preserve current portability debt.

### 8.7 Child tools

Go, Cargo, npm, Python, Clang, linkers, QEMU, and package managers have their own variables and internal conventions. Simple should project environment variables at process boundaries when isolation is required, but should not rewrite paths embedded in third-party caches or assume those caches are safe to share.

### 8.8 Performance

Putting all data under one physical directory can create large-directory and filesystem-contention regressions. Structured owner/version/digest sharding is mandatory. Root resolution must be cached per process/session rather than repeatedly querying Git, HOME, or environment variables on hot paths.

### 8.9 Existing command behavior

`simple cache path`, `simple cache clean`, bootstrap flags, MCP wrappers, explicit `--cache-root`, and CI cache keys are user-visible contracts. A migration needs compatibility output and must define whether `simple cache clean` cleans package cache only, all recomputable user caches, or a selected owner. It must never remove `state/`, `worktrees/`, or provenance evidence by default.

### 8.10 Tests that deliberately use foreign roots

Many tests set `TMPDIR` to an isolated fixture or the current directory to verify containment and residue behavior. The ratchet must allow test fixtures to model legacy/foreign environments while ensuring production paths consume the centralized resolver.

## 9. Highest-value hotspots

| Priority | Owner/files | Problem | Proposed destination |
|---:|---|---|---|
| 1 | `src/compiler/70.backend/backend/runtime_compiler.spl` | Reusable runtime-object cache is under OS temp; compiler probes use predictable PID names. | user `cache/runtime-objects/`; worktree/user session `tmp/compiler/`. |
| 2 | `src/compiler/70.backend/linker/mold.spl` | POSIX ignores `TMPDIR`; cleanup uses substring authorization. | worktree `tmp/linker/<run-id>/` with owned cleanup handle. |
| 3 | `src/compiler/80.driver/cache/cache_root.spl`, `scripts/bootstrap/lib/host-shared-cache.shs` | Best existing policy is duplicated and not platform-complete. | common two-root resolver plus generated/shared fixtures. |
| 4 | `config/mcp/mcp_startup_lib.shs` | Four path policies; hard-coded `/tmp`; cwd-name collision; mixed cache/state/log semantics. | worktree `cache/mcp`, `state/health`, `logs`, and `tmp`. |
| 5 | `scripts/release/converge-reviewed-fix.shs` and other worktree creators | Strong local checks but no global root/lease authority. | user `worktrees/<repo-id>/` plus user `state/leases/`. |
| 6 | `src/app/cache/main.spl` and package path/config families | Competing user cache locations and ambiguous cleanup authority. | user `cache/packages` and `cache/registry`, with migration command. |
| 7 | major `scripts/check/**`, `scripts/bootstrap/**`, `scripts/setup/**` | Hundreds of private `${TMPDIR:-/tmp}`/`mktemp` conventions. | sourced resolver and owner-scoped session allocation. |

## 10. Findings and recommendation

The repository already contains the necessary architectural ideas—host-shared immutable cache, lane-private mutable state, explicit bootstrap run roots, and safe external worktree validation—but they are implemented independently. The primary problem is not lack of environment variables; it is lack of one ownership and lifecycle model.

The proposed two-root model is feasible if it preserves semantic subdirectories and typed cleanup classes. “Only two places” must mean two authoritative roots, not two undifferentiated directories. Shared cache, temporary sessions, worktrees, mutable state, logs, builds, and provenance evidence need distinct descendants and cleanup rules.

Recommended requirement direction:

- adopt `SIMPLE_USER_STORAGE_ROOT` and `SIMPLE_WORKTREE_STORAGE_ROOT` as the only Simple-owned root authorities;
- retain legacy subsystem variables temporarily as exact leaf overrides;
- place reusable content-addressed caches and agent worktrees beneath the user root;
- place revision/configuration-sensitive cache, build, logs, evidence, and ordinary test/compiler scratch beneath the current-worktree root;
- prohibit reusable caches under OS temp and prohibit direct production `/tmp` use after migration;
- centralize cleanup around containment proofs and leases;
- migrate owners in waves with compatibility receipts and cache-key audits, not a global string replacement.

No implementation was performed in this research lane.
