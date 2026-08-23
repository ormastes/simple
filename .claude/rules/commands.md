---
alwaysApply: false
---
# Quick Commands Reference

```bash
# Build
bin/simple build                    # Prints bootstrap HELP and exits (~0.02s). Does NOT build.
bin/simple build bootstrap          # Seed-side Rust 3-stage self-compilation check ONLY.
                                    # NOT the sanctioned bootstrap: it never invokes
                                    # scripts/bootstrap/bootstrap-from-scratch.sh, skips the
                                    # receipt gate and planner admission, and builds no Stage 4
                                    # full CLI (misc_commands.rs:341). Use the script instead.

# Quality
bin/simple lint <changed .spl files> # Pure-Simple source linter
bin/simple build fmt                # Rust formatter
bin/simple build check              # Rust clippy + rustfmt check + Rust tests
sh scripts/check/check-dual-run-shadow.shs # C/Simple dual-run shadow gate (goal 6, binary_runtime_hardening plan)
sh scripts/check/check-perf-regression-tests.shs # Pins every landed perf fix by its mechanism (**176 mechanisms** as of 2026-08-23 — the long-standing "16 rows" figure here was stale; fail-closed, --selftest); caught f13adc2eca5 silently reverting the O(n^2) test-manifest reindex fix 8f3efdfbd65. Audit: doc/09_report/perf_regression_test_audit_2026-08-21.md

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

## The CLI `--help` is incomplete and partly wrong (measured 2026-08-23)

Do not treat `simple --help` as the command list. Measured by RUNNING the
deployed `bin/release/x86_64-unknown-linux-gnu/simple` (60,650,360 bytes,
2026-08-23 04:47), which announces itself as a **bootstrap seed**:

- **`--help` prints to stderr, not stdout.** `simple --help | grep x` returns
  nothing (measured: 0 lines on stdout, 226 on stderr). Redirect with `2>&1`.
- **39 commands listed vs 85 registered** in `src/app/cli/dispatch/table.spl`.
  Undocumented but working: `run`, `repl`, `fmt`, `check`, `fix`, `search`,
  `todo-scan`, `todo-gen`, `bug-add`/`bug-gen`/`bug-resolve`, `stats`,
  `doc-coverage`, `clean`, and ~44 more.
- **`build` is absent from `--help`** and is not a project build — its
  subcommands (`bootstrap`/`lint`/`fmt`/`check`) are Rust-workspace tooling.
  Compiling a program is `compile` / `native-build` / `run`.
- **`list`, `tree`, `install` are self-referential stubs**: `simple list` prints
  `Package management is handled by the Simple app. / Run: simple list`
  (`driver/src/cli/commands/pkg_commands.rs:9`). `update` and `cache` are
  advertised in `--help` and registered nowhere.
- **An unknown command is reported as a missing file** — `simple nosuchcmd` says
  `error: file not found: nosuchcmd`, because the argument falls through to the
  script-path route. A typo'd subcommand yields a nonsense diagnostic.

`table.spl` carries no help strings at all (`CommandEntry` is
`(name, app_path, env_override, needs_rust_flags)`); the help text lives in
`src/compiler_rust/driver/src/cli/help.rs`, which is why the two drift with
nothing to catch it. Record, REOPENED with these counts:
`doc/08_tracking/bug/cli_help_dispatch_drift_2026-08-11.md`.

## A `src/lib/**` change needs NO build (measured 2026-08-09)

Editing the stdlib requires **no build step at all** for `run` / `test` / lint /
LSP. The stdlib is read as SOURCE on every process start — measured by strace:
**82 opens of `src/lib/**.spl`, zero `.smf`**. **The 82 figure was corrected
2026-08-23 and must not be re-cited for startup cost:** re-measured with
`strace -f -c -e trace=openat,open,stat,mmap bin/simple run hello.spl`, a
hello-world run does **89 openat totalling 1.13 ms, of which 5 are `.spl`** —
file I/O is under 2 ms of a 76-144 ms run, and the startup floor is the 60.6 MB
binary (page-fault + reloc), not `.spl` reading. The **zero `.smf`** half, which
is what makes the no-build conclusion true, is unaffected. Evidence:
`doc/10_metrics/startup/cross_language_startup_benchmark_2026-08-18.md`
§Re-measurement 2026-08-23. Nothing is baked into the binary
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

- **`bin/simple lint` cost is FIXED STARTUP, not per-declaration and not
  superlinear (re-measured 2026-08-23).** ~37s of a ~44s lint is startup that
  happens before the linted file matters at all. The superlinear-in-content term
  the rows further down assert **no longer exists**, and the file those rows call
  unlintable now lints clean in under a minute.

  Measured on the deployed seed (`bin/release/x86_64-unknown-linux-gnu/simple`,
  60,536,008 bytes, mtime 2026-08-22 15:29:00,
  md5 `51cd42a27916f8d36f02f31d31fbe390`), shared box at load 43-53 / 32 cores —
  an idle box is faster, so treat wall numbers as an envelope. Every run printed
  `Lint passed: all files clean`, so these are completed runs, not early bails:

  | fixture | lines | top-level fns | wall | max RSS |
  |---|---|---|---|---|
  | trivial 1-fn | 2 | 1 | 37.9s | 397 MB |
  | `zca_rows.spl` prefix | 48 | 1 | 36.4s | 400 MB |
  | `zca_rows.spl` prefix | 293 | 5 | 39.2s | 390 MB |
  | `zca_rows.spl` prefix | 633 | 10 | 39.1s | 391 MB |
  | `zca_rows.spl` prefix | 1,170 | 16 | 37.0s | 450 MB |
  | **`zca_rows.spl` FULL** | **1,901** | **30** | **44.3s** | **587 MB** |

  Cost is **flat**: a ~950x growth in declaration content adds ~6.4s total. The
  full file went from the `>2400s (killed)` recorded below to **44.3s — >54x**.

  **Root cause of the ~37s, located 2026-08-23 and fixed in `617b58a9ffa`.** It
  is not the linter and not the linted file: it is the HIR import loader
  re-PARSING imported modules. `preregister_imported_type_names` and
  `load_imported_types` (`hir/lower/import_loader.rs`) each did
  `read_to_string -> CRLF normalize -> Parser::new -> parse()` on **every `use`
  statement naming a module**. On a lint of a **two-line** file that is **3,819
  successful `.spl` `openat` over 423 distinct files**, with
  `10.frontend/core/ast.spl` **fully parsed 866 times**. Cost is driven by the
  COMPILER's own import graph, not by your input — which is exactly why the
  trivial and the 1,901-line fixture cost the same, and why `test` and `run` pay
  it too. `parsed_imported_module()` memoizes the parsed module per PROCESS
  (never on disk — the "edit `src/lib`, no build needed" property above is
  load-bearing): **3,819 -> 676 opens (5.65x)**, same 423 distinct files,
  `ast.spl` 866 -> <=4, heavy-file wall median 33.86s -> 24.45s (~28%), at a cost
  of **+~110 MB max RSS**. On the trivial fixture the wall change is within
  noise and no gain is claimed.

  **You will not feel this until a seed redeploy.** The fix is in
  `src/compiler_rust`; the deployed `bin/simple` predates it.

  **Do not batch files** — 2 files exceeded 600s vs 119s for 1 (2026-08-17
  measurement, not re-checked).
  Cost is pinned by `sh scripts/check/check-lint-cost-budget.shs` (fail-closed,
  `--selftest`, treats a silent exit 0 with no verdict line as FAIL); its
  thresholds were calibrated to the pre-fix regime and should be re-derived.
  Startup is **not** the ~310s fixed `Session setup` cost seen in
  `bin/simple test`; lint does not share that path. Don't conflate the two.
  Audit: `doc/09_report/tooling_latency_audit_2026-08-23.md`. Resolved record:
  `doc/08_tracking/bug/lint_timeout_hwir_zca_rows_2026-08-17.md`.

- **Profiling trap: `SIMPLE_INTERP_SAMPLE` and `SIMPLE_LOADER_TRACE` emit
  NOTHING from the deployed seed** (measured 2026-08-23 on runs lasting 37-44s:
  no `$SIMPLE_INTERP_SAMPLE_OUT.<pid>` file, no stderr dump, no loader summary).
  Both exist in `src/compiler_rust` at `main`; the deployed binary predates them.
  Attach-based profiling is separately blocked on this host (`ptrace_scope=1`,
  `perf_event_paranoid=4`). Two lanes have now been defeated by this. What works
  today, without any cooperation from the binary:

  ```bash
  # WHERE the reads come from — level-gated call-site attribution, default OFF.
  SIMPLE_READ_TRACE=1 bin/simple lint file.spl 2>&1 | grep '^\[read\]' \
    | awk '{print $2}' | sort | uniq -c | sort -rn | head
  # HOW MANY — needs nothing built in.
  strace -f -e trace=openat -o /tmp/st.txt bin/simple lint file.spl
  ```

  `SIMPLE_PERF_COUNTERS=1` prints the interpreter counter table at exit,
  including `IMPORT_AST_PARSES`/`IMPORT_AST_HITS` and
  `PROBE_SOURCE_READS`/`PROBE_SOURCE_HITS` — pin perf work by these COUNTS, not
  by wall clock: identical work measured 15.05s-27.95s on this box, a spread
  wider than most fixes.

- **SUPERSEDED 2026-08-23 — retained for history, do NOT delete, do NOT use for
  planning.** The rows below assert a superlinear-in-content term and call
  `zca_rows.spl` unlintable. Both claims were true when measured and are false
  now (see the flat table above: the same full file, 44.3s, clean). The
  2026-08-18 caveat that these rows "MUST be re-measured before use" has now been
  discharged by that re-measurement, so the claim is replaced rather than
  re-caveated.

  <details><summary>Historical: 2026-08-17 rows (superseded)</summary>

  `bin/simple lint` cost ~12s fixed startup, then a per-declaration cost that
  **depends on what is IN the declaration**. The older "~3.3-4.0s per function
  decl" figure was measured on simple declarations. Re-measured 2026-08-17
  (shared box, load 33-55, 21-30 concurrent `simple` processes):

  | fixture | decls | lines | wall | per decl |
  |---|---|---|---|---|
  | 1 trivial fn | 1 | 2 | 12s | — (this is startup) |
  | 15 tiny fns | 15 | 61 | 111s | ~6.6s |
  | 90 tiny fns | 90 | 361 | 436s | ~4.7s |
  | 4 fns x 45 stmts | 4 | 192 | 107s | ~24s |
  | 45 fns x 4 stmts | 45 | 315 | 239s | ~5s |
  | `zca_rows.spl` first 2 fns | 2 | 182 | 210s | ~99s |
  | `zca_rows.spl` first 8 fns | 8 | 443 | **>2400s** (killed) | >300s |

  Conclusions drawn at the time — the first still holds, the second does not:
  - **Declaration count alone scales LINEARLY** (15 -> 90 decls leaves per-decl
    cost flat or falling). Splitting a file into more functions does not help.
  - ~~**Content complexity is the real driver, and it is superlinear in the
    file.**~~ **REFUTED 2026-08-23**: cost is flat across 2..1,901 lines of the
    very file this claimed was unlintable.

  Interim note (2026-08-18): after the 06:12 seed redeploy (env-cache + parser
  fixes), a 501-line / 125-fn generated arithmetic file linted in ~76s and a
  tracked fixture went 49s -> 14s. Numbers:
  `doc/10_metrics/startup/cross_language_compute_compile_benchmark_2026-08-18.md`.

  </details>
- Lint IS pure Simple and IS wired — the old "no pure-Simple binary can
  lint" claim here was a category error. `bootstrap/stage3/simple lint` does
  say `unknown command` (exit 1), but stage3 is built from
  `src/app/cli/bootstrap_main.spl`, the BOOTSTRAP cli, which by design
  exposes only `compile` and `native-build` (dispatch `:459-492`). It has no
  `run`, `test`, `fmt` or `build` either, so probing it for `lint` proves
  nothing. The implementation is `src/app/cli/lint_entry.spl` ->
  `app.io.cli_lint_commands` with rules in `src/app/lint/main.spl` and
  `src/compiler/90.tools/lint/`, wired at `dispatch/table.spl:113-118`. It
  runs end to end in ~6s and its findings discriminate (clean fixture ->
  `Lint passed`, dirty -> `warning[RAW-RT-001]`). Pinned by
  `scripts/check/check-pure-simple-lint-runnable.shs`. The real gap is that
  no FULL-CLI pure-Simple binary is deployed, not a missing lint port.
  `simple test` GREEN still does not prove self-hosted.
- Detail: `doc/07_guide/tooling/build_fast_path.md`

## LLVM toolchain (pinned to 23.1.0, 2026-08-21)

```bash
. scripts/setup/llvm-toolchain-env.shs   # SOURCE it. Exports CC=clang-23,
                                         # CXX=clang++-23, LD=ld.lld-23,
                                         # LLVM_CONFIG=llvm-config-23, and puts
                                         # LLVM 23's bin dirs first on PATH.
SIMPLE_LLVM_VERSION=20 . scripts/setup/llvm-toolchain-env.shs   # explicit fallback
```

clang/LLD/llvm-config **23.1.0** (apt.llvm.org snapshot
`1:23.1.0~++20260818083557+55feb0a3b6b7`), deployed WITHOUT root by extracting
the `.deb`s into `/mnt/data/toolchains/llvm-23-root` — this host has no
passwordless sudo. Old pin, clang 20.1.8, stays as the fallback.

**Setting `CC` alone is not enough.** The seed's native link step picks its
linker by probing PATH for a bare `ld.lld`
(`src/compiler_rust/compiler/src/pipeline/native_project/linker.rs:1972`,
`use_direct_lld`) and never reads `$CC`/`$LD` — so with only the suffixed
binaries on PATH you get clang 23 compiling and LLD **18** linking. The env
script fixes this by also putting the UNSUFFIXED `usr/lib/llvm-23/bin` ahead of
`/usr/bin`; that is the no-root equivalent of update-alternatives and is why
sourcing it (not just exporting `CC`) is the documented path.

Measured 2026-08-21: the C runtime gate is **byte-identical** on 23 and 20
(108 clean, same 1 pre-existing failure in
`src/runtime/test/rt_browser_renderer_namespace_selfcheck.c:55,57` — undeclared
`browser_renderer_*`, reproduces on clang-20, NOT caused by 23), the runtime
archive builds clean under 23, `cargo check --release --bin simple` passes, and
a hello-world `native-build` runs with `Linker: Ubuntu LLD 23.1.0`.
**Still on LLVM 18: the seed's `llvm` cargo feature** — inkwell publishes no
`llvm23-*` feature (0.10.0, latest, tops out at `llvm22-1`; `llvm-sys` has only
`231.0.0-rc2`), so that pin was deliberately left alone.
Detail: `doc/07_guide/infra/toolchain/llvm_23_deploy_2026-08-21.md`

## Setup
```bash
scripts/setup/setup.shs          # Create bin/simple symlink (auto-detects platform)
sh config/mcp/install.shs # Install MCP config
```
