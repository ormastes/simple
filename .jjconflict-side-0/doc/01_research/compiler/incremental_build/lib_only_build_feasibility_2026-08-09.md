# Lib-only build feasibility — can a `src/lib/**`-only change skip bootstrap?

Date: 2026-08-09
Status: research (no source touched, nothing committed)
Related: `doc/05_design/compiler/semantic_incremental_build_cache_aop_formal_2026-08-09.md`,
`doc/03_plan/compiler/cache/semantic_incremental_build_v2_plan_2026-08-09.md`

## TL;DR

**The premise is false, and that is the good news.** A `src/lib/**`-only change
needs **no build at all** for the interpreted lanes (`bin/simple run`,
`bin/simple test`, LSP, MCP). The stdlib is plain `.spl` source read fresh from
disk on every process start — nothing is baked into the compiler binary, and no
on-disk stdlib artifact is consulted. The edit-test loop for a lib tweak already
costs ~0.03–0.6 s, not a 3-stage bootstrap.

**And `bin/simple build` does not bootstrap.** Measured: a bare `bin/simple
build` prints help and exits 0 in 0.01 s. `CLAUDE.md` and
`.claude/rules/commands.md` ("Debug build (runs bootstrap by default)") are
**wrong for the deployed binary**.

The real cost is confined to the **native/AOT lane**, and there the existing
lever (`--entry-closure`) was measured **not** to contain the module graph.

---

## 0. The hypothesis, tested directly

> **HYPOTHESIS:** the project bootstraps everything rather than only the needed
> parts because it has no TARGET and DEPENDENCY model — no build graph of targets
> with edges, so the only safe unit of work is "everything".

**Verdict: CONFIRMED for the native/AOT lane, with one correction to the
premise.** The correction: the project does not, in fact, bootstrap on a lib
change — it does not bootstrap at all unless asked (§1a). But *why* nothing
smaller than "everything" can be built when you do need a native artifact is
exactly the stated reason: **the graph data structures exist and are dead code.**

### 0.1 Is there a notion of a *target*? — **No. Files only.** (MEASURED)

`/usr/bin/grep -rn "struct BuildTarget\|struct Target\b" src/compiler/80.driver --include=*.spl`
finds **no build-target type**. The single `struct Target`
(`src/compiler/80.driver/smf_writer.spl:27`) is an SMF *relocation* target, not a
buildable unit. There is no named unit with declared inputs and outputs anywhere
in the driver. The unit of work is a **source file**, and the unit of output is a
`.o` keyed by content hash.

### 0.2 Is the dependency info traversed to compute a minimal rebuild set? — **No, twice over.** (MEASURED)

The data exists. `src/compiler/80.driver/driver_build/incremental.spl` (702 lines)
defines `FileFingerprint` (:154), `DependencyEntry{source, fingerprint,
dependencies, outputs}` (:195-200), `IncrChangeSet` (:236), `detect_changes`
(:493), `get_changed_symbols` (:602), `has_cached_object` (:447),
`get_cached_outputs` (:471), `integrity_check` (:539).

**Failure 1 — it is a predicate, not a traversal.**
`DependencyEntry.needs_recompile` (:203-226) checks the file's own fingerprint,
then loops over `self.dependencies` — its **direct** imports only. It never
recurses, never walks reverse edges, never topologically orders anything. It
answers *"is this one file stale, y/n"*. There is no code that turns a change set
into a minimal rebuild set, and no `topolog*`/`reverse_deps`/`transitive` symbol
exists anywhere under `src/compiler/80.driver`.

**Failure 2 — the model is not wired in at all.** Every importer of
`driver_build.incremental` takes only the fingerprint/identity helpers, never the
graph:

| importer | imported symbols |
|---|---|
| `src/compiler/70.backend/build_native.spl:28` | `FileFingerprint`, `native_build_cache_scope_key`, `native_build_compiler_identity` |
| `src/compiler/80.driver/driver_aot_native_output.spl:28` | `BuildCache`, `FileFingerprint`, `native_build_cache_scope_key`, `native_build_compiler_identity` |
| `src/compiler/80.driver/driver_bootstrap.spl:27` | `native_build_compiler_identity` |
| `src/compiler/80.driver/driver_vhdl_artifact_build.spl:9` | `native_build_compiler_identity`, `native_build_compiler_executable_hash` |

`DependencyEntry`, `detect_changes`, `IncrChangeSet`, `get_changed_symbols`,
`has_cached_object` are imported by **nobody**. `needs_recompile` in this file is
**never called**. There are additionally two *other* unreferenced
`needs_recompile` implementations —
`src/compiler/80.driver/incremental.spl:97` and
`src/compiler/80.driver/incremental_builder.spl:207` — i.e. three parallel dead
incremental engines.

**Failure 3 — the content-addressed identity layer is dead too.** As the
hypothesis states: `src/compiler/80.driver/cache/action_key.spl` and
`cache/cas_store.spl` have **zero external callers** (`/usr/bin/grep -rn
"cas_store\|action_key" src --include=*.spl` returns only self-references plus
the unrelated `src/lib/nogc_async_mut/gpu/store/cas_store.spl`). Confirmed by
`src/compiler/80.driver/cache/__init__.spl:25-28`, which exports `cache_types`,
`compile_options_hash`, `cache_validator`, `lazy_section` — and **not**
`action_key`, **not** `cas_store`. Both files cite the Phase-1 plan
`doc/03_plan/compiler/cache/global_cas_interpreter_cache_option_c_plan_2026-07-24.md`
in their headers. So `ActionKey{module_id, iface_digest, deps, cfg_features,
ct_env_inputs}` — the one structure in the repo that actually encodes *dependency
interfaces* into a build identity — is written, sorted, digested
(`action_key.spl:156-191`), and never used by any load path.

**Symbol-key collision (hypothesis point 2) — CONFIRMED as written, but it is
not what forces full rebuilds.** `incremental.spl:645` (`name.replace("/", "_")`)
and `:663` (`func_name.replace("/", "_")`) sanitise MIR cache filenames, so
`a/b` and `a_b` collide. Real, but moot: `get_cached_mir_functions` (:629) sits
behind the same never-imported surface. The conservatism it would cause is
unreachable.

**What actually runs instead.** The live native cache is the Rust seed's
per-module object cache (`src/compiler_rust/compiler/src/pipeline/native_project/mod.rs`,
§2): a flat map from *content hash of one module's own source text* → `.o`. No
edges. Which is why its key omits dependency content (§5 caveat) — you cannot
fold in something you never modelled.

### 0.3 What forces the full rebuild — real dependency or missing mechanism?

**Both, cleanly separable:**

* **For the edit-test loop (`run`/`test`/lint/LSP): MISSING MECHANISM is not even
  needed — nothing is forced.** MEASURED (§2, §4): the stdlib is read from source
  on every process start, 82 `.spl` opens and 0 artifacts. A lib change is live
  immediately. Any bootstrap run for this reason is pure waste, caused by the
  documentation (§6/R1), not by the build system.
* **For a native artifact: MISSING MECHANISM.** There is no real dependency
  forcing a whole-tree compile of a 4-line program. MEASURED (§3): `--entry-closure`
  still pulled in `src/compiler/**` and `src/app/**` and ran past 6 minutes. With
  a target model and a traversable graph, the rebuild set for a `src/lib` change
  would be *that module plus its reverse-reachable set*, which for the ~90 % of
  `src/lib` the compiler never imports (§5) is empty.
* **For deploying a new compiler binary: REAL DEPENDENCY**, but only for the
  enumerated subtrees in §5 (`nogc_sync_mut/io/**`, `log`, `io_runtime`,
  `string_core`, `text`, `platform`, `path`, `array`, `binary_io`,
  `common/{string_core,crypto/sha256,target,sdn}`, `tooling/easy_fix`,
  `sffi/llvm`). The compiler is written in Simple and does import std — that part
  of the hypothesis's caveat is true and cannot be engineered away. Everything
  else under `src/lib` is unreachable from the compiler.

### 0.4 Sizing the fix

The pieces are already written; what is missing is wiring and a traversal.

| step | what | cost | risk |
|---|---|---|---|
| A | Emit a real edge set: persist `DependencyEntry.dependencies` from the resolver the driver already runs, keyed by `ActionKey` (`cache/action_key.spl` — exists, unused) | small | low |
| B | Add reverse-edge traversal: change-set → transitive closure of importers → rebuild set. This is the single missing algorithm; `needs_recompile` is a one-hop predicate today (`incremental.spl:203`) | small–medium | low |
| C | Wire `cas_store`/`action_key` into the object-cache load path so the key includes dependency interface digests (closes the §5 soundness hole) | medium | medium |
| D | Introduce a target type (named unit + declared inputs/outputs) so `src/lib` can *be* a target and `build lib` means something | medium | medium |
| E | Delete two of the three dead `needs_recompile` engines | small | low |

B is the highest value per unit of effort and is the literal crux: without it,
the dependency data being collected can only ever answer y/n per file.

---

## 0bis. Would target builds + interface-hash verification remove the bootstraps?

> **"Does the project bootstrap everything rather than only the needed parts
> because it lacks a TARGET-based build (like npm or cmake)? If Simple had target
> builds, plus INTERFACE HASH VERIFICATION for dynamic loading, or an INTERFACE
> VERSIONING spec — would that remove the need for these bootstraps?"**

**Short answer: the mechanism is fully designed and partly written, and
essentially none of it is wired in. It exists on paper and in dead code, not in
any executed path.** Target builds + interface-digest verification would
**eliminate** the bootstrap for the ~90 %+ of `src/lib` the compiler never
imports, and **reduce** it — from *every* change to *interface-changing* changes
only — for the small remainder. It cannot reach zero, because the compiler is
written in Simple and genuinely imports std.

### 1. Target model — does Simple have named targets with inputs/outputs and edges?

**A project manifest format exists. The build does not read it.** (MEASURED)

There are four `simple.sdn` manifests — `src/lib/simple.sdn`,
`src/compiler/simple.sdn`, `src/app/simple.sdn`, `src/compiler_rust/simple.sdn`.
`src/lib/simple.sdn` is a genuine package declaration:

```
project:
  name: simple-std
  version: 1.0.0-beta
  type: library
  source_dir: src
  dependencies:
    - project: ../../rust
```

Name, version, type, **and inter-project dependency edges** — the skeleton of an
npm/cmake target. But `/usr/bin/grep -rn '"simple.sdn"' src/compiler src/app`
finds only **four** consumers, and **none is a build path**:
`src/app/info/main.spl:116` (display), and
`src/app/io/_CliCommands/handler_commands.spl:128,163,283` (reads a *lint
profile*; the comment at `:128` even flags it as untestable). No compiler,
driver, or native-pipeline module reads it. **`dependencies:` is never traversed
by anything.**

So: **files only.** No `struct BuildTarget` in the driver (§0.1); the manifest
that could name a target is inert; the unit of work is a source file and the unit
of output is a content-hashed `.o`. This is the npm/cmake gap, exactly as the
question frames it.

### 2. Interface hash — does InterfaceDigest already exist? **Implemented, and called by nobody.** (MEASURED)

This is the sharpest finding in the whole document.

`src/compiler/80.driver/cache/action_key.spl:197-204` implements it, correctly
and canonically, citing the plan:

```
# InterfaceDigest — downstream-visible semantics only. Parts are a SET of
# canonical interface-item texts; sorted here so callers need not pre-sort.
fn interface_digest_of(parts: [text]) -> text:
    val sorted = action_key_sort_texts(parts)
    ...
    sha256_text(canon_field("simple/interface/v1", canon_seq(items)))
```

`ActionDep` carries `iface_digest` (`:33`), deps sort on
`(module_id, iface_digest)` (`:86-91`), and it is encoded into the action key as
`ifaceDigest` (`:149`).

**`/usr/bin/grep -rn "interface_digest_of" src --include=*.spl` returns exactly
1 line — its own definition. Zero callers.** Nothing ever supplies `parts`;
nothing ever consumes the result. Likewise `iface_digest` appears only inside
`action_key.spl` itself. And as established in §0.2, `action_key.spl` is not even
exported by `src/compiler/80.driver/cache/__init__.spl:25-28`.

So the answer to *"is it computed and then ignored, like `action_key.spl`?"* is
worse than that: **it is not even computed.** It is a correct function sitting in
an unreachable file.

The v2 protocol is likewise paper. `src/compiler/80.driver/cache/schema/cache_protocol.sdn`
is **887 lines** specifying the whole thing —
`:189` `deps … type: set<dep>, class: KEY`;
`:222` *"dependency module id + INTERFACE digest, not full content digest"*;
`:314-316` `{module_id, iface_digest}` ordered;
`:92` `interface: "simple/interface/v1"`; plus advice/aspect interface digests at
`:409-500`. **`/usr/bin/grep -rn "cache_protocol" src` returns nothing — no
`.spl` and no `.rs` file reads this schema.**

**Plainly: the interface-digest mechanism exists on paper (887-line schema) and
as one uncalled function. It exists in code but not in any executed path.**

Meanwhile the cache that *does* run is content-keyed, in both engines:
* Rust seed object cache — `object_cache_key` hashes the module's **own source
  text** (`native_project/mod.rs:1425-1445`), no dependency component at all.
* `SmfManifestEntry` (`src/compiler/80.driver/watcher/smf_manifest.spl:23-34`)
  carries `source_hash: i64` — a **content** hash — plus backend/opt/flags. **No
  interface or export digest field exists.**

That is the whole problem in one line: *content* keys mean any body edit
invalidates downstream; *interface* keys would not.

### 3. Dynamic loading / interface versioning — is any manifest verified at load?

**A manifest exists; nothing verifies it on a load path.** (MEASURED)

`SmfManifest{version, entries, updated_at}` (`smf_manifest.spl:36-39`, schema
version 3) is written and read only by the **watch daemon** —
`src/compiler/80.driver/watcher/watcher_daemon.spl:149,172` (`update_smf_manifest_entry`)
and `:187` (`load_smf_manifest_default`, `smf_manifest_find`). Outside
`watcher/`, no module in `src/` references `smf_manifest`. It is not consulted by
`bin/simple run`, by `test`, or by the native pipeline — consistent with the
strace in §2, which recorded **0 `.smf` opens** across 82 stdlib loads.

So there is no interface-versioning check at load time, and nothing to check
against: the manifest records a content hash, not an interface digest, so even if
a loader read it, it could only answer *"did the bytes change"*.

**Could a rebuilt lib be swapped in without relinking the compiler, if a loader
verified interface digests?** For the dynamic path, **yes in principle** — and
note `native-build` already defaults to `--mode dynload`
(`compile_targets.spl:816`) and can emit archives/objects, so the artifact shape
is there. The missing pieces are (a) an interface digest recorded in the SMF/LSM
manifest and (b) a load-time comparison against the digest the consumer was
compiled against. Both are specified in the Option C plan; neither is
implemented. **INFERRED**, since no such swap was attempted here.

### 4. Verdict: eliminate, or only reduce?

**Reduce sharply, and eliminate for most of the tree — never fully eliminate.**

The residual is exactly as the question anticipates: the compiler is written in
Simple and imports std, so a std change that alters an **interface** the compiler
consumes must still rebuild the compiler. A change to a **private body** would
not — and today it does, because the live keys are content hashes.

**Quantifying what fraction of `src/lib` the compiler actually imports**
(MEASURED, direct imports; `src/lib` totals 7,630 `.spl`):

| `src/lib` subtree | files | compiler files importing it |
|---|---|---|
| `nogc_async_mut/` | 1,829 | **0** |
| `gc_async_mut/` (ml, gpu, cuda, torch) | 1,385 | **0** |
| `gc_sync_mut/` | 868 | **0** |
| `hardware/` | 195 | 1 |
| `editor/` | 122 | **0** |
| `skia/` | 104 | **0** |
| `scv/`, `scipy/`, `viz/`, `js/`, `gui/`, `blink/` | 81 | **0** each |
| `nogc_sync_mut/` | 1,907 | only `io/` (70 files) |
| `common/` | 826 | a handful (`string_core`, `crypto/sha256`, `target`, `sdn` = 9 files) |

Summing the provably-zero trees alone: **≥ 4,389 of 7,630 files (≥ 57.5 %) are
untouchable by any compiler rebuild**, by direct import. Adding the untouched
bulk of `nogc_sync_mut/` and `common/`, the directly-named compiler surface is
**~85 files, ≈ 1.1 %** of `src/lib`. The true transitive closure is larger than
85 and smaller than the whole tree — it was **not measured** (measuring it needs
the resolver, and the only run that would have shown it exceeded the time budget,
§3). A defensible statement: **the compiler touches on the order of 1–10 % of
`src/lib`; ~90 %+ is provably irrelevant to the compiler.**

Therefore:

* **Target builds alone** would eliminate the bootstrap for the ~90 %+ of
  `src/lib` outside the compiler's closure — a change to `gc_async_mut/ml/**`
  can, with edges, be *proven* not to reach the compiler. This is the big win and
  needs no interface digests at all, only §0.4 step B (reverse-edge traversal).
* **Interface-digest verification** then handles the remaining ~1–10 %: a body
  edit to `src/lib/nogc_sync_mut/io/file_ops.spl` leaves its interface digest
  unchanged, so downstream compiler modules keep their cached objects and no
  rebuild is required. This converts "every change to the compiler's std surface"
  into "only signature/layout/effect changes to it".
* **Residual, irreducible:** an interface-altering change to the compiler's own
  std surface (~85+ files) still requires rebuilding and redeploying the
  compiler. No amount of caching removes that — it is a real dependency.

**Honest bottom line: none of this is a missing design. It is a designed,
partly-written, entirely-unwired mechanism.** The 887-line protocol, the
canonical `interface_digest_of`, the `ActionKey` with sorted dependency interface
digests, the `DependencyEntry` edge type, the `simple.sdn` dependency
declarations — all present, all unreferenced. The work is integration, not
invention: wire `simple.sdn` deps into the driver as targets; supply `parts` to
`interface_digest_of` from the resolver's export table; add the reverse-edge
traversal (§0.4 B); add an interface-digest field to `SmfManifestEntry` and check
it at load. Sizing from §0.4: steps A–D, small-to-medium each, the traversal
being the crux.

---

## Binary identity (recorded with every timing below)

```
readlink -f bin/simple  → /home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple
stat -c '%s %y'         → 29577536   2026-08-09 04:50:31.571562013 +0000
```

This binary prints on every invocation:

> `WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.`

i.e. **it is the Rust seed**; no self-hosted binary is deployed
(`doc/08_tracking/bug/no_self_hosted_binary_deployed_blocks_bootstrap_gate_2026-08-09.md`).
Every measurement below is therefore a *seed* measurement. Where the pure-Simple
`build` CLI differs from the seed's, both are described.

---

## 1. What `bin/simple build` actually does today

There are **two divergent `build` CLIs**, and the deployed binary exposes the
Rust one.

### 1a. Deployed (Rust seed) — MEASURED

```
$ /usr/bin/time -f 'REAL %e' bin/simple build
  simple build <command> [options]
  COMMANDS:
    bootstrap   3-stage self-compilation verification
    lint        Run clippy linter on Rust workspace
    fmt         Run rustfmt on Rust workspace
    check       Run lint + fmt --check + tests
    help        Show this help
REAL 0.01
EXIT=0
```

* A bare `build` is a **help screen**, not a build. Exit 0.
* `lint` / `fmt` / `check` here operate on the **Rust workspace** (clippy,
  rustfmt), not on `.spl` sources. They are irrelevant to a `src/lib` change.
* `bootstrap` is the only subcommand that compiles anything (3-stage). Not run
  here — it monopolises the machine.

### 1b. Pure-Simple `build` — `src/app/build/cli_entry.spl`

`fn handle_build` (`src/app/build/cli_entry.spl:43-77`):

| arg | route |
|---|---|
| `lint` | `cli_run_lint` (:53-54) — pure-Simple `.spl` linter |
| `fmt` | `cli_run_fmt` (:56-57) |
| `check` | `run_check` (:59-60) |
| `simpleos [arch…]` | `scripts/ci/build-simpleos-toolchain.shs` (:62-63, :19-41) |
| *(anything else, incl. `bootstrap`)* | `cli_native_build` (:65-77) |

**`bootstrap` and the default are the same code path.** `:69` only strips
`args[0]` so it is not mistaken for a source path; there is no separate 3-stage
logic in this entry point (the 3-stage lives in `scripts/`). And with no entry
file, `cli_native_build` **errors out** rather than building the world:

`src/app/io/_CliCompile/compile_targets.spl:747-750`
```
if entry_point == "":
    _cli_eprint("Error: No entry point specified for native-build backend")
```

### Which lanes recompile the stdlib?

| lane | stdlib treatment |
|---|---|
| `bin/simple run <f.spl>` | parsed from `src/lib/**/*.spl` **every process start** (interpreted) |
| `bin/simple test` | same — interpreted |
| `build lint` / `build fmt` / `build check` (pure-Simple) | parse only; no artifact |
| `build` / `build bootstrap` → `native-build` | full AOT compile; per-module `.o` cache |
| `build simpleos` | full AOT per target triple |

### Is there already an undocumented lib-only path?

**Partly.** `cli_native_build` already accepts, undocumented in CLAUDE.md:

* `--source <dir>` (repeatable) — `compile_targets.spl:857-861`
* `--entry-closure` — "Compile only modules reachable from `--entry`
  (suppresses the driver's implicit whole-src bulk-load)" — `:832-836`
* `--emit-object` / `--emit-archive` — `:876-880`, mutually exclusive at `:842`
* `--cache-dir <dir>` (default `build/native_cache`) — `:911-919`
* `--clean`, `--no-incremental`, `--threads/-j`

So the *flags* for "compile this subtree into an archive" exist. What does not
exist is a `build lib` subcommand, and — see §3 — `--entry-closure` did **not**
actually contain the graph in the measured run.

---

## 2. How `src/lib/**` is consumed

**Resolution.** `use std.X` is path-anchored to the repo's stdlib roots; there is
no override.

* Rust seed, interpreter:
  `src/compiler_rust/compiler/src/interpreter_module/path_resolution.rs:394`
  (`is_stdlib_rooted`: first segment ∈ `std|lib|std_lib|verification`),
  `:425` (`for lib_root in ["src/lib", "src/std"]`), `:631-652` (std is
  *anchored*, deliberately un-shadowable), `:799-802` root list.
* Rust seed, compile path:
  `src/compiler_rust/compiler/src/module_resolver/resolution.rs:410,417,430,582,645,652`
  — `stdlib_roots = [project_root/"src/lib", project_root/"src/std"]`;
  also `module_resolver/types.rs:415-418`. `src/std` is a symlink to `lib`, so
  both roots are the same tree.
* Pure-Simple: `src/compiler/10.frontend/core/interpreter/module_loader_resolve.spl:7,15,276`;
  `src/compiler/99.loader/module_loader.spl`;
  `src/compiler/70.backend/build_native_pipeline.spl:348,359`.

**Source vs artifact — MEASURED by syscall trace.**

```
strace -f -e trace=openat bin/simple run probe2.spl     # use std.fs + std.json
  opens matching src/lib/**.spl : 82
  opens matching src/lib/**.smf : 0
```

The stdlib is read as **source, every run**. The only caching is in-process
(`src/compiler_rust/compiler/src/module_cache.rs:322,334`, keyed by normalised
path; `:109-116` deliberately *retains* `src/lib/` entries on selective clear) —
it dies with the process.

There are 38 stray `.smf` files under `src/lib` against 7,630 `.spl`
(`find src/lib -name '*.smf' | wc -l` → 38). **Zero were opened.** They are
vestigial; `.smf` is a resolvable module format
(`module_resolver/resolution.rs:205-224`) and a deferred-monomorphisation
template store (`monomorphize/deferred.rs`), not a stdlib distribution artifact.

**Native lane cache** (the only on-disk one):
`src/compiler_rust/compiler/src/pipeline/native_project/mod.rs`
* dir `<project_root>/.simple/native_cache[/<triple>]` — `:544-560`; objects at `:734`
* hit/miss on `objects/{hash:016x}.o` — `:909-921`, `:1042`
* key = `object_cache_key` `:1425-1445` — **content hash of the module's source
  text**, plus is_entry, backend, no_mangle, module_prefix, opt_level,
  `SIMPLE_NATIVE_CPU`, SIMD tier, `compiler_fingerprint()`; folded with
  `GlobalBuildFingerprint::combined()` (`:875`, `:1547-1568`). **No mtime
  anywhere** — content-addressed.
* Measured size on this machine: `du -sh .simple/native_cache` → **12M**.

---

## 3. Measured cost

All timings on the seed binary identified above, foreground, this machine.

| what | command | REAL |
|---|---|---|
| no-op `build` | `bin/simple build` | **0.01 s** (help only, exit 0) |
| run, tiny std import | `bin/simple run probe.spl` (`use std.common.text`) | **0.03 s** |
| run, 2 std trees | `bin/simple run probe2.spl` (`use std.fs`, `use std.json`) run 1/2/3 | **0.59 / 0.62 / 0.53 s** |
| same, after touching a lib file | — | **0.03 s** (no rebuild step exists to trigger) |
| native-build, 4-line entry, `--entry-closure` | `bin/simple native-build --entry probe2.spl -o … --entry-closure` | **never completed** — killed at the 2-min bound on attempt 1; attempt 2 ran **~13 min** and was killed by the researcher (`rc=143`) with **no output binary produced** |

Cold-vs-warm for the interpreted lane is effectively **flat** (0.59 → 0.62 →
0.53): there is no artifact to warm, only the OS page cache. The variance is
noise.

**The native-build number is the finding.** Its log shows that a 4-line entry
with `--entry-closure` still pulled in and diagnosed:

* `src/compiler/10.frontend/…`, `20.hir/…`, `35.semantics/…`, `50.mir/…`,
  `70.backend/…`, `80.driver/…`, `90.tools/…`
* `src/app/io/…`, `src/app/build/…`
* `src/lib/text.spl`, `src/lib/platform.spl`, `src/lib/string_core.spl`,
  `src/lib/common/json/parser.spl`, `src/lib/nogc_sync_mut/path.spl`

i.e. `--entry-closure` did **not** suppress the whole-src bulk-load in this
invocation — the compiler's own tree was compiled to build a hello-world. That
is the actual cost centre, and it is not caused by `src/lib` at all.

---

## 4. What breaks if you skip bootstrap after a lib change?

**Nothing, for interpreted lanes.** Proven three ways:

1. Syscall trace: 82 `src/lib/**.spl` opens per run, 0 `.smf` (§2).
2. No embedded stdlib. `/usr/bin/grep -rn "include_str!\|include_bytes!"` over
   non-vendor `src/compiler_rust` finds **no `include_str!` of any `src/lib`
   file**. The only `.spl` inclusions are test-only and point at
   `src/compiler/**`:
   `pipeline/native_project/tests.rs:18,19,212`.
   `runtime/src/compress/self_extract.rs:94` is commented out.
3. `strings -a "$(readlink -f bin/simple)" | grep -c 'src/lib/'` → **3**, and all
   three are **path literals** used by the resolver / lint messages
   (`"src/lib"`, `"src/lib/std/src"`,
   `src/lib/nogc_async_mut/concurrent/multicore_green.spl` as a lint constant).
   Zero stdlib *bodies*.

So the stdlib is **not baked in**. There is nothing to relink.

**What does break:** the *native/AOT* artifacts under `.simple/native_cache` and
any previously linked binary in `bin/release/**` still carry the **old** lib
code, because they were compiled from the old source. Those are stale until
rebuilt — but that is true of any AOT artifact and is not "bootstrap".

---

## 5. Minimal correct dependency rule

Let `L` = the set of changed files, all under `src/lib/**`.

**Skip any build when** the consumer is an interpreted lane
(`bin/simple run`, `bin/simple test`, `build lint`, `build fmt`, `build check`,
LSP, MCP). Condition: *always*. The change is live on the next process start,
unconditionally, because resolution is by path into the live worktree and there
is no artifact in between. No exceptions were found.

**Rebuild is required only when** you need a **native artifact** whose module
graph contains a changed lib module — i.e. you are about to run something out of
`build/native/**`, `bin/release/**`, or a SimpleOS target. Then rebuild *that
artifact*, not the bootstrap.

**Bootstrap (3-stage) is required only when** you intend to *deploy a new
compiler binary*, i.e. when the change alters behaviour the compiler itself
depends on **and** you want the deployed `bin/release/<triple>/simple` to reflect
it. The compiler-dependency set is real and large:

* **239 of 1,567** `.spl` files under `src/compiler/` contain a top-level
  `use std.` (`/usr/bin/grep -rlE '^ *use std\.' src/compiler --include=*.spl`).
* **75 distinct** `std.*` import prefixes in `src/compiler/` alone; **69 distinct
  first-segment submodules** across `src/compiler` + `src/app`.
* Heaviest, in order: `std.nogc_sync_mut.io.{file_ops,process_ops,dir_ops,time_ops,env_ops,sysinfo_ops}`
  (≈100 sites), `std.log` (23), `std.tooling.easy_fix{,.types}` (40),
  `std.io_runtime` (37), `std.string_core` / `std.common.string_core` (19),
  `std.text` (11), `std.platform` (10), `std.common.crypto.sha256` (8),
  `std.binary_io` (8), `std.common.target` (7), `std.sffi.llvm` (4),
  `std.path`, `std.array`, `std.common.sdn.parser`, `std.cli.cli_util`.

So: **`src/lib/nogc_sync_mut/io/**`, `src/lib/{log,io_runtime,string_core,text,platform,path,array,binary_io}*`,
`src/lib/common/{string_core,crypto/sha256,target,sdn}/**`, `src/lib/tooling/easy_fix/**`,
`src/lib/sffi/llvm/**`** are compiler dependencies. Everything else under
`src/lib` (ui, gpu, ml, game2d, web_framework, tui, database, http_server, …) is
**not** reachable from the compiler and can never require a bootstrap.

Even for the dependency set, the rule is *"bootstrap before deploying a new
compiler"*, not *"bootstrap before testing your change"* — because the compiler
running your test is reading your new lib source anyway.

### Soundness caveat (INFERRED, not measured)

The native object cache key (`object_cache_key`, `mod.rs:1425-1445`) hashes **the
module's own source text**, plus global build knobs and the compiler binary
fingerprint. It does **not** appear to include the content of that module's
*dependencies*. If any cross-module information is baked into an object —
monomorphised generics (`monomorphize/deferred.rs`), struct layout, inlined
constants — then changing a lib module's *signature or layout* leaves its
importers' cached objects **stale but hash-valid**. `compiler_fingerprint()`
(`mod.rs:1367`, hashes the compiler exe bytes) rescues the case where the
*compiler* changed, but not the case where only a *lib dependency* changed. This
is precisely the hole Semantic Incremental Build v2 is meant to close, and it is
the one thing that could make a naive "lib-only build" silently wrong. **It was
not empirically falsified here** — verifying it needs a signature-change
experiment on a shared worktree, which this research deliberately did not run.

---

## 6. Recommendation

**Best outcome first: for the common case, nothing needs building, and the
cheapest correct change is documentation.**

### R1 — Fix the docs (cost: minutes, risk: none) — *highest value*

`CLAUDE.md` and `.claude/rules/commands.md` say `bin/simple build` is a "Debug
build (runs bootstrap by default)". Measured: it prints help and exits 0 in
0.01 s. Every agent that has run a bootstrap "because a lib file changed" has
burned a machine-hour on a false premise. Replace with:

> A `src/lib/**`-only change requires **no build**. Run `bin/simple test <spec>`
> directly — the stdlib is read from source on every run. Bootstrap only before
> deploying a new compiler binary.

Add to `.claude/rules/bootstrap.md` the compiler-dependency subtree list from §5.

### R2 — Add `bin/simple build lib` (cost: small, risk: low)

A thin subcommand in `src/app/build/cli_entry.spl` next to the existing
`simpleos` arm:

```
if subcmd == "lib":
    return cli_native_build(["native-build", "--source", "src/lib",
                            "--emit-archive", "--entry-closure", ...])
```

Every flag it needs already exists (`--source`, `--emit-archive`,
`--entry-closure`, `--cache-dir`). Value: a **parse/type-check fence** for lib
changes and a reusable archive for the native lane. Risk: low, but see R3 — it
is worthless until `--entry-closure` actually closes.

### R3 — Fix `--entry-closure` (cost: medium, risk: medium) — *the real win*

MEASURED: a 4-line entry compiled with `--entry-closure` still dragged in
`src/compiler/**` and `src/app/**` and exceeded 6 minutes. Until the closure is
honoured, **no** subtree-scoped build can be fast, lib-only or otherwise. This
should be filed as a bug against the native pipeline and is a prerequisite for
the Semantic Incremental Build v2 plan delivering a user-visible speedup.

### R4 — Extend the object cache key to dependency content (cost: medium, risk: medium)

Close the §5 caveat: fold each module's resolved-import content digest into
`object_cache_key`. This is the Semantic Incremental Build v2 design's core and
is what would make a lib-only native rebuild *correct*, not just fast.

---

## MEASURED vs INFERRED

**MEASURED (commands run, output read):**
binary identity and seed banner; `bin/simple build` = help + exit 0 in 0.01 s;
run timings 0.03 s / 0.59 / 0.62 / 0.53 s; strace 82 `src/lib/*.spl` opens vs 0
`.smf`; 38 `.smf` vs 7,630 `.spl` under `src/lib`; no `include_str!` of `src/lib`
in non-vendor Rust; 3 `src/lib` strings in the binary, all path literals;
`.simple/native_cache` = 12M; 239/1,567 compiler files import `std`; 75 distinct
`std.*` prefixes in `src/compiler`; native-build with `--entry-closure` > 120 s
and loading `src/compiler/**` + `src/app/**`; **no `struct BuildTarget` in
`src/compiler/80.driver`**; **`DependencyEntry`/`detect_changes`/`get_changed_symbols`/
`has_cached_object` imported by zero modules** (the four importers of
`driver_build.incremental` take only fingerprint/identity helpers);
**`action_key.spl` and `cache/cas_store.spl` have zero external callers and are
not exported by `cache/__init__.spl:25-28`**; three separate unreferenced
`needs_recompile` implementations; `replace("/","_")` key sanitisation at
`incremental.spl:645,663`; no `topolog*`/`transitive` symbol under `80.driver`;
**`interface_digest_of` has exactly one occurrence in `src/` — its own definition
(zero callers)**; **`cache_protocol.sdn` (887 lines) has zero readers in `src/`**;
`simple.sdn` read only by `app/info` and a lint-profile helper, never by a build
path; `SmfManifestEntry` carries `source_hash` (content) and **no** interface
digest field; `smf_manifest` referenced only inside `80.driver/watcher/`;
`src/lib` subtree counts and the zero-compiler-import result for
`gc_async_mut`/`gc_sync_mut`/`nogc_async_mut`/`skia`/`editor`/`viz`/`js`/`gui`/
`blink`/`scipy`/`scv` (≥4,389 of 7,630 files).

**INFERRED (read from source, not executed):**
the pure-Simple `build` dispatch table and the "no entry point" error — the
deployed seed never reaches that code, so it was read, not run; the object cache
key's omission of dependency content and the resulting staleness risk; the claim
that `.smf` files under `src/lib` are vestigial (proven unopened for *these two*
imports, not for all of `src/lib`); the compiler-dependency subtree list, derived
from import-site grep rather than from a resolved module graph; the claim that a
load-time interface-digest check would permit hot-swapping a rebuilt lib without
relinking (no such swap was attempted); the "~1–10 % of `src/lib` is in the
compiler's closure" range — the 1.1 % direct-import figure and the ≥57.5 %
provably-unreachable figure are measured, the transitive closure between them is
not.

**NOT ATTEMPTED (deliberately):**
`bin/simple build bootstrap` (monopolises the machine, other agents active); any
mutation of tracked files in the shared working copy; a signature-change
experiment to falsify the cache-soundness caveat.
