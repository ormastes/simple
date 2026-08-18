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
`DependencyEntry.needs_recompile` (`driver_build/incremental.spl:280`) is a
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
  `(module_id, iface_digest)`. **`/usr/bin/grep -rn interface_digest_of src`
  returns 4 lines (all under `src/compiler`): its own definition
  (`cache/action_key.spl:199`), one schema row
  (`cache/schema/cache_protocol.sdn:844`), and two comments that merely name it
  (`35.semantics/interface/compile_interface.spl:37`,
  `cache/block/block_key.spl:10`). Zero actual CALL SITES — never computed, not
  merely ignored.** (The count matters only so the claim can't be dismissed as
  sloppy; the load-bearing part is the zero callers.)
- The caches that DO run are content-keyed: `object_cache_key` hashes only the
  module's own source; `SmfManifestEntry` carries `source_hash` and has no
  interface-digest field. The manifest ROW *is* verified on the interpret path —
  `driver_api_interpret.spl:55` calls `smf_manifest_entry_matches_source` and
  fails closed to a full interpret on mismatch. What is unwired is the
  whole-entry wrapper `smf_manifest_entry_verifies`
  (`watcher/smf_manifest.spl:134`), which re-reads `entry.source_path` itself:
  it is exported from `watcher/__init__.spl:33` and has zero callers.

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
`interface_digest_of`, `simple.sdn` traversal, and `smf_manifest_entry_verifies`
— all still uncalled. (Row-level manifest verification is NOT in that list: it
already runs on the interpret path, see above.) Design:
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

- `bin/simple lint` costs ~12s fixed startup, then a per-declaration cost that
  **depends on what is IN the declaration**. The old "~3.3-4.0s per function
  decl" figure here was measured on simple declarations and is roughly right for
  those, but it is NOT what makes a big file unlintable, and reading it as a
  general rule under-predicts real compiler files by more than an order of
  magnitude. Re-measured 2026-08-17 (shared box, load 33-55, 21-30 concurrent
  `simple` processes — an idle box is faster, so treat these as an envelope):

  | fixture | decls | lines | wall | per decl |
  |---|---|---|---|---|
  | 1 trivial fn | 1 | 2 | 12s | — (this is startup) |
  | 15 tiny fns | 15 | 61 | 111s | ~6.6s |
  | 90 tiny fns | 90 | 361 | 436s | ~4.7s |
  | 4 fns x 45 stmts | 4 | 192 | 107s | ~24s |
  | 45 fns x 4 stmts | 45 | 315 | 239s | ~5s |
  | `zca_rows.spl` first 2 fns | 2 | 182 | 210s | ~99s |
  | `zca_rows.spl` first 8 fns | 8 | 443 | **>2400s** (killed) | >300s |

  Two conclusions the old line got wrong:
  - **Declaration count alone scales LINEARLY** (15 -> 90 decls leaves per-decl
    cost flat or falling). Splitting a file into more functions does not help.
  - **Content complexity is the real driver, and it is superlinear in the file.**
    Two real hwir row-builder functions cost 20x two trivial ones, and going
    from 182 to 443 lines of the same file multiplied cost by more than 11x for
    2.4x the lines. That is why `src/compiler/50.mir/hwir/zca_rows.spl` (30 such
    functions, 1901 lines) exceeds any practical budget — it is a cost problem,
    **not a hang**: the linter does terminate and does print a verdict.
  - Startup is ~12s and is **not** the ~310s fixed `Session setup` cost seen in
    `bin/simple test`; lint does not share that path. Don't conflate the two.

  **Do not batch files** — 2 files exceeded 600s vs 119s for 1.
  Cost is pinned by `sh scripts/check/check-lint-cost-budget.shs` (fail-closed,
  `--selftest`, treats a silent exit 0 with no verdict line as FAIL).
  Open: the superlinear term has not been located — attach-based profiling is
  blocked on this host (`ptrace_scope=1`, `perf_event_paranoid=4`). See
  `doc/08_tracking/bug/lint_timeout_hwir_zca_rows_2026-08-17.md`.
  **Dated note (2026-08-18): the table above predates the 2026-08-18 06:12 seed
  redeploy (env-cache + parser fixes) and MUST be re-measured before use.** The
  root cause tracked in that bug is now fixed and deployed; remeasured on the
  new binary, a 501-line / 125-fn generated arithmetic file lints in ~76s (vs
  the pre-fix 436s for a smaller 90-fn fixture), and a tracked fixture went
  49s -> 14s. Old rows are retained for history only; do NOT delete them. Fresh
  numbers:
  `doc/10_metrics/startup/cross_language_compute_compile_benchmark_2026-08-18.md`.
- No pure-Simple binary can lint: `bootstrap/stage3/simple lint` is
  `unknown command` (exit 1). `simple test` GREEN does not prove self-hosted.
- Detail: `doc/07_guide/tooling/build_fast_path.md`

## Setup
```bash
scripts/setup/setup.shs          # Create bin/simple symlink (auto-detects platform)
sh config/mcp/install.shs # Install MCP config
```
