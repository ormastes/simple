# Per-Lane Private Build Caches

Status: implemented (2026-08-17). Scope: native-build object caches in both
engines (Rust seed `native_project`, pure-Simple `80.driver`) and the bootstrap
stage scripts.

## Problem

The bootstrap now runs multiple concurrent lanes — phase-1 seed, phase-2 stage,
phase-3 self-host, phase-4 full-CLI/tools, plus census and tool-build lanes.
Each lane may use a **different compiler binary** against the **same source
tree**, and today they all share one `build/bootstrap/native_cache`. A cache
entry produced by the phase-2 compiler can therefore be picked up by a phase-3
lane. A fix landing mid-run makes a stale entry silently wrong.

## What already existed (survey, 2026-08-17)

| Mechanism | Location | State |
|---|---|---|
| `--cache-dir` | `driver/src/cli/native_build.rs:216`, `native_all/src/lib.rs:309` | wired; one dir shared by all lanes |
| `object_cache_key` | `compiler/src/pipeline/native_project/mod.rs:1458` | folds content, entry-ness, backend, mangle, prefix, opt, CPU, SIMD tier **and `compiler_fingerprint()`** (hash of `current_exe` bytes) — compiler identity was already covered on this path |
| `cache_dir()` | same file, `:596` | `<base>[/<triple>]` — no scope segment |
| `native_build_cache_scope_key` | `src/compiler/80.driver/driver_build/incremental.spl:180` | folds backend/cpu/features/opt/**compiler identity** (`exe=…;compiler=…;runtime=…;bundle=…`), used as a **cache subdirectory** name at `driver_aot_native_output.spl:90-93` |
| `interface_digest_of` | `cache/action_key.spl:197` | canonical `simple/interface/v1` digest, **zero callers**; `action_key.spl`/`cas_store.spl` not exported from `cache/__init__.spl` |
| `src/lib/simple.sdn` `dependencies:` | — | real target edges, no build path traverses them |
| `SmfManifest` / `SmfManifestEntry.source_hash` | loader | written, never verified on load |
| `cache_scope_key` | `scripts/check/lib/bootstrap-planner-admission-bound.shs` | `sha256(runtime_snapshot:planner_source_closure_snapshot)` — the shape reused here |

So **compiler identity was already in both keys**. The missing axis is the one
that motivated this work: the **lane**. Two lanes can legitimately run the *same*
compiler binary (phase-4 tools vs. census) and still must not share entries, and
— more importantly — a lane must be able to *declare* its cache as private
rather than rely on an implicit fingerprint that a mid-run redeploy can change
underneath it.

This design deliberately does **not** touch `interface_digest_of`,
`SmfManifest` verification, or `simple.sdn` traversal. Those are the *partial
rebuild* problem; this is the *cross-lane isolation* problem. They are recorded
above so the next reader does not re-survey.

## Design

### Cache scope key

```
lane        = $SIMPLE_CACHE_SCOPE            (default: "default")
scope_key   = <existing content/producer key>  ⊕  lane  ⊕  compiler identity
```

Following `bootstrap-planner-admission-bound.shs`'s `cache_scope_key` shape
(a digest over the identities that must bind an entry), the scope is composed,
not invented: the existing key already carries compiler identity, so the change
is **additive** — one `lane=` field.

Two enforcement layers, both required:

1. **Directory partition.** Cache entries live under a scope-derived
   subdirectory. A cross-scope lookup cannot even name an out-of-scope entry, so
   the MISS is structural rather than dependent on a hash comparison.
   - pure-Simple: already the case — the scope string *is* the directory name
     (`driver_aot_native_output.spl:92`); adding `lane=` to the scope string
     partitions the directory automatically.
   - Rust: `cache_dir()` gains a `scope-<hex>` segment.
2. **Key fold.** `lane` is folded into `object_cache_key` too, so even a
   hand-pointed shared directory produces different keys per lane.

### Marker file

Each cache directory carries `.cache_scope` recording `lane` and the compiler
identity that last wrote it. It exists so **scripts** can check ownership
without running a compiler (the bootstrap guard below), and so a mismatched
directory is detectable rather than silently reused.

### CLI / env surface

| Surface | Meaning |
|---|---|
| `--cache-scope <name>` (native-build, native-all) | declares this lane's scope; sets `SIMPLE_CACHE_SCOPE` for the process |
| `SIMPLE_CACHE_SCOPE=<name>` | same, for scripts and child processes |
| unset | `default` — behaves exactly as before for a single-lane build; no user-visible change |

The default is safe because a single-lane build has exactly one scope, and
compiler identity (already in both keys) still separates different binaries.
Explicit beats implicit: a lane that cares says `--cache-scope phase3`.

### Bootstrap scripts

Each stage gets `build/bootstrap/native_cache/<lane>/` instead of a shared
`native_cache`, with `<lane>` = the stage name. Before each stage build a
fail-closed guard (`scripts/check/check-cache-scope-ownership.shs`) reads the
directory's `.cache_scope` marker: matching scope ⇒ reuse; different scope ⇒
**FAIL**, naming both scopes (refuse, do not silently switch — a silent switch
hides a script bug). Verdict is the last stdout line, `PASS`/`FAIL`/`ERROR`
(exit 0/1/2), nothing-checked is ERROR, and `--selftest` runs fixtures first.

## Non-goals

- Partial / dependency-aware rebuild (`interface_digest_of`, `simple.sdn`).
- `SmfManifest` load-time verification.
- Any change to what makes an entry *content*-valid.
