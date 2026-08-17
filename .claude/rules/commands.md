---
alwaysApply: false
---
# Quick Commands Reference

```bash
# Build
bin/simple build                    # Prints bootstrap HELP and exits (~0.02s). Does NOT build.
bin/simple build bootstrap          # 3-stage self-compilation verification

# Quality
bin/simple lint <changed .spl files> # Pure-Simple source linter
bin/simple build fmt                # Rust formatter
bin/simple build check              # Rust clippy + rustfmt check + Rust tests

# Documentation Coverage
bin/simple stats                    # Doc coverage in stats
bin/simple doc-coverage             # Terminal coverage report
bin/simple doc-coverage --missing   # Show undocumented items

# Tools
bin/simple fix file.spl --dry-run   # Preview fixes
bin/simple todo-scan                # Update TODO tracking
bin/simple bug-add --id=X           # Add bug
bin/simple bug-gen                  # Generate bug report
```

## A `src/lib/**` change needs NO build (measured 2026-08-09)

Editing the stdlib requires **no build step at all** for `run` / `test` / lint /
LSP. The stdlib is read as SOURCE on every process start — measured by strace:
**82 opens of `src/lib/**.spl`, zero `.smf`**. Nothing is baked into the binary
(no `include_str!` of `src/lib`; only 3 `src/lib` strings, all path literals),
so no relink is needed either.

```bash
# edit src/lib/... then just run it. No build.
bin/simple test test/01_unit/.../foo_spec.spl
```

**Bootstrap is only for DEPLOYING A COMPILER**, not for picking up a lib change.
When you do need it, the genuine dependency set is 239 of 1567 compiler files
that import std, across 75 prefixes (`nogc_sync_mut/io/**`, `log`, `io_runtime`,
`string_core`, `text`, `platform`, `path`, `array`, `binary_io`,
`common/{crypto/sha256,target,sdn}`, `tooling/easy_fix`, `sffi/llvm`).

Why there is no partial build: there is **no target/dependency model**. No
`BuildTarget` exists in `80.driver` — only files.
`DependencyEntry.needs_recompile` (`driver_build/incremental.spl:203-226`) is a
ONE-HOP predicate that never recurses, and is **never called** — its four
importers take only fingerprint helpers. `action_key.spl` / `cas_store.spl` have
zero external callers and are not exported from `cache/__init__.spl`.
Detail: `doc/01_research/compiler/incremental_build/lib_only_build_feasibility_2026-08-09.md`.
(NOT under `.../compiler/build/` — `.gitignore:106 build/` silently swallows any
path containing a `build/` component, and `git add` on it is a silent no-op.)

**The mechanism to fix this is designed and written, but wired to nothing:**
- `src/lib/simple.sdn` already declares `name/version/type: library/dependencies:`
  — real target edges. Read only by `src/app/info/main.spl:116` (display) and a
  lint-profile reader. **No build path traverses `dependencies:`.**
- `action_key.spl:197-204` implements `interface_digest_of` canonically
  (`simple/interface/v1`), with `ActionDep.iface_digest` and dep sort on
  `(module_id, iface_digest)`. **`grep -rn interface_digest_of src` returns one
  line: its own definition. Zero callers — never computed, not merely ignored.**
- The caches that DO run are content-keyed: `object_cache_key` hashes only the
  module's own source; `SmfManifestEntry` carries `source_hash` and has no
  interface-digest field. `SmfManifest` is written but never verified on load.

**Partly superseded 2026-08-17 — "content-keyed" was never the whole story, and
is now less of it.** `object_cache_key` (`native_project/mod.rs`) already folded
`compiler_fingerprint()` (a hash of `current_exe`'s bytes) alongside backend,
opt-level, CPU and SIMD tier, and the pure-Simple `native_build_cache_scope_key`
(`src/compiler/80.driver/driver_build/incremental.spl`) already folded a full
producer identity (`exe=…;compiler=…;runtime=…;bundle=…`) used as the cache
SUBDIRECTORY name. Both now additionally carry a **lane** axis —
`SIMPLE_CACHE_SCOPE`, or `--cache-scope <name>` on the Rust native-build /
native-all CLIs — because two concurrent bootstrap lanes can legitimately share a
compiler binary and still must not share entries. Entries are partitioned by a
scope-derived DIRECTORY, so a cross-scope lookup cannot name an out-of-scope
entry; unset ⇒ `default`, identical to previous behaviour. Bootstrap stages get
`build/bootstrap/native_cache/<lane>/` plus a fail-closed ownership guard
(`scripts/check/check-cache-scope-ownership.shs`, `.cache_scope` marker).
What is NOT superseded: dependency-aware / partial rebuild. That still needs
`interface_digest_of`, `simple.sdn` traversal, and `SmfManifest`
load-verification — all still uncalled. Design:
`doc/05_design/compiler/incremental_build/per_lane_private_caches.md`.

## Fast Path (measured 2026-08-09)

```bash
# Cached lint — 152.00s cold -> 0.03s warm. Caches CLEAN verdicts only;
# findings and edited files always re-lint. Verdict line is last on stdout.
sh scripts/check/lint-cached.shs src/lib/common/base_encoding.spl
SIMPLE_LINT_CACHE=0 sh scripts/check/lint-cached.shs <files>   # bypass

# ALWAYS record binary identity with any timing — the symlink target is
# replaced by other agents mid-session (3 distinct builds seen in one session).
readlink -f bin/simple && stat -c '%s %y' "$(readlink -f bin/simple)"

# Provenance probe: bin/simple is currently the RUST SEED, and says so.
bin/simple --version 2>&1 | head -2

# grep here is a wrapped ugrep honouring .gitignore (measured 4 hits vs 17).
/usr/bin/grep -rn "pattern" src/       # exhaustive scans / censuses
```

- `bin/simple lint` costs ~11.7s startup + ~3.3-4.0s **per function decl**,
  superlinear. A 120-line file takes ~119s. **Do not batch files** — 2 files
  exceeded 600s vs 119s for 1.
- No pure-Simple binary can lint: `bootstrap/stage3/simple lint` is
  `unknown command` (exit 1). `simple test` GREEN does not prove self-hosted.
- Detail: `doc/07_guide/tooling/build_fast_path.md`

## Setup
```bash
scripts/setup/setup.shs          # Create bin/simple symlink (auto-detects platform)
sh config/mcp/install.shs # Install MCP config
```
