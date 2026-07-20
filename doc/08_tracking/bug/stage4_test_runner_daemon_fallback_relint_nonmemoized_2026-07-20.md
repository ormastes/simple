# Stage-4 self-hosted daemon-fallback relint/compile traversal is non-memoized
# and dominates `simple test`/`simple run` wall time on specs with broad
# private/internal imports (e.g. `arch_check_spec.spl`) — this, not
# `strip_ansi`/`parse_test_output`, is the actual driver of the 550s+ hang
# reported in
# doc/08_tracking/bug/stage4_test_runner_strip_ansi_superlinear_hang_2026-07-20.md

**Date:** 2026-07-20
**Severity:** high (any spec whose imports force the "test daemon
unavailable; running directly [fallback]" path to shell out and
lint/compile a broad slice of the compiler's own internal module graph can
stall `simple test`/`simple run` on the self-hosted binary for minutes+ —
observed exceeding 900s without completing)
**Status:** CLOSED (root-fixed) — 2026-07-20 root-fix lane, own worktree
`/tmp/wt_relint` at `6b793e5d2b2`. Root cause was **not** missing
memoization of a per-file relint (that framing, inherited from this doc's
own "recommended next steps" §, is falsified below) — it was an
over-eager, unfiltered `export use` re-export chain that pulled the
*entire compiler* (~250 files) into any consumer of `app.io.mod`/
`app.io.cli_ops`, including light consumers that use neither `cli_compile`
nor `cli_run_lint`. Fixed in `.spl` by removing the redundant re-export;
`bin/simple test test/01_unit/app/arch_check_spec.spl` went from >900s
(timeout, never completing) to **~14.5s wall** (Passed: 74, Failed: 0).
See "2026-07-20 root-fix lane" section below for the full trace, the
falsification of the "659 repeats" reading, and the fix.

## Origin

A prior lane (`doc/08_tracking/bug/stage4_test_runner_strip_ansi_superlinear_hang_2026-07-20.md`)
investigated a 550s+ stall running `simple test test/01_unit/app/
arch_check_spec.spl` on the self-hosted stage-4 binary and localized it (via
3 gdb backtraces) to the self-hosted `parse_test_output`/`strip_ansi` call
chain, while separately noting — but not confirming as the cause — that the
daemon-fallback path re-lints ~205 distinct compiler-internal `.spl` files,
each repeated tens to hundreds of times (up to 659x for one file), which is
"a naive non-memoized traversal of a highly-connected internal module
graph... worth its own investigation."

A follow-up root-fix lane (same date) microbenchmarked `strip_ansi` /
`parse_test_output` directly (see that doc's "2026-07-20 follow-up" section)
and found them **empirically linear**, not quadratic: full production volume
(424,554 lines) extrapolates to ~13-20s of parse time, not 550s+. That lane
also ran `SIMPLE_EXECUTION_MODE=cranelift simple run test/01_unit/app/
arch_check_spec.spl` directly — which reproduces the daemon-fallback relint
+ spec execution but calls `parse_test_output` **zero times** (parsing only
happens in the parent process under `test`) — and it did **not finish within
a 900s timeout**. That reattributes the 550s+ hang to this relint traversal
and closes out the strip_ansi investigation. This doc exists to track the
relint traversal itself as the real, still-open root cause.

## Evidence

1. **`run arch_check_spec.spl` alone exceeds 900s.** `SIMPLE_EXECUTION_MODE=cranelift
   timeout 900 build/bootstrap/full/x86_64-unknown-linux-gnu/simple run
   test/01_unit/app/arch_check_spec.spl` (binary at commit `3835e717d16`,
   `/tmp/wt_deploy`) was killed by the timeout, having produced 149,478+
   lines (~11MB, tail truncated by the kill) of lint output and never
   reaching the spec's own assertions. This path never calls
   `parse_test_output` (that only happens in the parent `test` process
   parsing the *captured* child output) — so 900s+ here is entirely
   compile/lint cost, not parse cost.
2. **Importing `std.test_runner` under `run` alone (no spec content at all)
   also exceeds 900s.** A separate minimal harness that only did `use
   std.test_runner.{strip_ansi, parse_test_output}` at the top and otherwise
   did nothing was killed at 900s without ever reaching its own `main()`.
   This confirms the cost is in module-graph relinting triggered by the
   *import*, independent of any specific spec's assertions or size.
3. **Repeated-file evidence from the original doc (§2 there):** direct `run`
   reproduction shows ~205 distinct compiler-internal `.spl` files each
   relinted repeatedly — up to 659x for one file
   (`_MirToLlvm/core_codegen.spl`), 616x for another
   (`_MirLoweringExpr/method_calls_literals.spl`), and double-digit-to-
   triple-digit repeats for ~18 more files in just one 20s/5MB snapshot.
   Per-file repeat counts were confirmed **byte-identical** across two
   different seed builds (pre- and post- two unrelated landed fixes),
   showing the repetition is a structural property of the traversal, not
   input-dependent noise.
4. **Seed vs NEW gap reconciled by this, not by strip_ansi:** the original
   doc's fair, load-controlled comparison showed `seed_baseline_bin`
   (native Rust) completing the same spec (with its own ~424K-line
   daemon-fallback dump) in ~32s while NEW stalled indefinitely under
   identical load. The seed's `test` subcommand is native Rust and never
   enters the self-hosted relint code path at all — so the seed's speed
   here reflects native Rust module-graph handling (whatever it is)
   vastly outperforming the self-hosted binary's own compiler-internal
   lint/compile traversal for this same workload.

## What's NOT yet known (why this is still OPEN, not root-caused)

This lane confirmed *where* the time goes (daemon-fallback relint of the
compiler's internal module graph, triggered by `arch_check_spec.spl`'s 12
underscore-prefixed private-symbol imports from `app.cli.arch_check`, or by
any import that pulls in the same graph) but did **not** pinpoint the
specific call site responsible for the non-memoized repetition. Candidates,
none confirmed:
- The daemon-fallback path may re-resolve and re-lint each transitively
  imported module fresh for every *reference* to it in the dependency graph
  (i.e. no "already visited" set keyed by module path), rather than once
  per unique file.
- The relint may be invoked once per *diagnostic-eligible declaration* in
  each importing file rather than once per file.
- The 659x/616x/etc. repeat counts roughly track module fan-in (how many
  other modules import that file) rather than a simple linear pass, which
  is consistent with a naive "for each import, recursively re-lint its
  whole subtree" traversal with no memo table — but this was not traced
  into the actual call site in this lane.

## Recommended next steps for a fix lane

1. Find the daemon-fallback / private-symbol-import relint entry point
   (likely near whatever triggers the "test daemon unavailable; running
   directly [fallback]" message and the subsequent Rust-seed delegation
   described in the original doc's §2) and identify the traversal that
   repeats per-file.
2. Add a "already linted this file path this run" memo set (a `Set<text>`
   or equivalent keyed by canonical file path) around that traversal —
   per the original mission's guidance, only do this if it is a cheap,
   clearly-safe memoization (this doc does not yet confirm that it is;
   confirm the traversal has no legitimate reason to re-lint the same file
   with different context/config before adding the memo).
3. Re-run `SIMPLE_EXECUTION_MODE=cranelift simple run test/01_unit/app/
   arch_check_spec.spl` before/after with a wall-clock timer to confirm the
   fix; target should be roughly seed-parity (~30s) or better, since the
   per-file repeat counts (~205 files, up to 659 repeats) suggest a
   memoized traversal could plausibly collapse this to a small fraction of
   the current cost.
4. Once fixed, re-scope the original smoke-matrix gate on
   `arch_check_spec.spl` back to blocking (both docs currently recommend
   excluding/soft-failing it pending a fix).

## Deploy recommendation

Same as the original doc: this is a pre-existing, self-hosted-only defect,
not introduced by any recently-landed change under test in that
investigation. `arch_check_spec.spl` (and any spec with a similarly broad
private-symbol import footprint) should remain excluded from hard-gating
smoke matrices, or be marked as a known, tracked, non-blocking failure
referencing this doc, until a fix lands here.

## 2026-07-20 root-fix lane

Own worktree `/tmp/wt_relint`, based on `main@6b793e5d2b2`. Verified before
starting that `bin/simple test test/01_unit/app/arch_check_spec.spl` still
reproduces the hang on this tip (>60s bounded probe: 169,775 stderr lines,
timed out — same shape as the original report).

### The "659 repeats" reading was a misdiagnosis — falsified by direct check

Reproduced the exact scenario with `SIMPLE_EXECUTION_MODE=cranelift ./bin/simple
run test/01_unit/app/arch_check_spec.spl` under a bounded timeout and captured
raw stderr (`grep -oE '^\s*--> [^:]+\.spl'`). This *does* reproduce the
`_MirToLlvm/core_codegen.spl` × 659 count this doc's §2 (and the sibling
strip_ansi doc) reported. But checking the **exact `file:line:col` triples**
behind those 659 lines (`grep -oE 'core_codegen\.spl:[0-9]+:[0-9]+' | sort -u`)
shows **all 659 are distinct locations** — core_codegen.spl (1563 lines) was
parsed **exactly once** and produced 659 separate "Common mistake detected"
lint findings scattered through the file (~1 finding per 2.4 lines — the
compiler's own source trips this lint rule pervasively). Not a re-parse; one
parse with a very noisy diagnostic. This falsifies the "up to 659 repeats"
framing this doc's Evidence §3 and the sibling strip_ansi doc's Evidence §2
both used to describe the mechanism — there is no 659× re-parse to memoize.

(There *is* a small amount of genuine re-parsing — a handful of "hub" files
like `driver.spl` showed the *exact same* `(line, col, source-line, caret)`
diagnostic emitted twice back-to-back, up to ~4× total across a run — but
this is a minor, secondary effect: across a full run, unique `file:line:col`
triples were ~80% of total emitted diagnostic lines. It was not chased
further because the dominant cost (below) fully explains the hang and a
targeted fix eliminates the vast majority of the wasted work; the residual
~4× duplication on a few hub files is a candidate for a small follow-up if
it ever shows up as material on its own.)

### The real mechanism: an unfiltered `export use` chain pulls in the whole compiler

Traced with a sequence of minimal, standalone reproductions (`use X (name)`
+ empty `main()`, run under a bounded timeout, counting unique
`/src/compiler/*.spl` paths touched):

- `use std.io_runtime (file_read)` — **instant, 0 compiler files** (control).
- `use app.cli.arch_check (_str_trim, ...)` (arch_check_spec.spl's own
  import) — reproduces the hang, ~250 compiler files touched.
- `use app.cli.arch_check (scan_arch_rules)` (public name, not
  underscore-prefixed) — **also** reproduces it. Ruled out "private-symbol
  import" as the trigger for the traversal itself (it is still the trigger
  for the *daemon-unavailable fallback*, see Angle B below, but not for the
  relint volume).
- `use app.cli.arch_check` (Single/whole-module import, not Group) — **also**
  reproduces it.
- `use app.io.mod (shell)` (arch_check_spec.spl's *other* import, unrelated
  to arch_check.spl entirely) — **also** reproduces it, alone, with no
  arch_check import at all.
- `use std.io_runtime (file_read)` stays clean throughout — confirms this is
  not a general "any import is slow" issue, it's specific to `app.io.mod`
  (and, separately, `app.cli.arch_check`).

Root-caused `app.io.mod`'s path: `app.io.mod` imports
`app.io.cli_ops.{get_args, exit, ..., context_generate, ..., settlement_main,
fault_set_*}` (all locally-defined or lightweight names). `app/io/cli_ops.spl`
itself, however, unconditionally re-exported three unrelated,
compiler-heavy blocks:

```
export use app.io._CliCommands.run_commands.{cli_run_code, cli_run_lint, cli_run_fmt, ...}
export use app.io._CliCommands.handler_commands.{cli_handle_web, ..., cli_watch_daemon}
export use app.io._CliCompile.compile_opt_and_driver.{cli_compile}
export use app.io._CliCompile.compile_targets.{cli_native_build}
```

`run_commands.spl` directly imports `compiler.driver.driver_api_core`,
`compiler.tools.{formatter,fix,lint}.main`, `compiler.core.lexer_struct`,
etc. — i.e. the real compiler pipeline, which `cli_run_lint`/`cli_compile`
genuinely need. The module loader's flatten-on-import logic
(`load_module_with_imports_internal` in
`src/compiler_rust/compiler/src/pipeline/module_loader.rs`) recurses into
**every** `export use` target of a flattened file unconditionally — it does
not filter by which names the *original* caller actually requested
(`should_keep_selective_export` only filters what's kept in the *returned*
item list, after the recursive load — and thus the cost — already
happened). So importing **anything** from `cli_ops.spl` (even a single
locally-defined name like `shell`) transitively force-loads
`run_commands.spl` → the entire compiler, ~250 files, regardless of
relevance. This is a real architectural bug (missing name-filtering in the
Rust loader's flatten recursion) with a low-risk, `.spl`-only mitigation
available: `cli_ops.spl` didn't need those three blocks at all —
`src/app/io/cli_commands.spl` and `src/app/io/cli_compile.spl` already
exist as the *intended* clean re-export homes for exactly this content
(both carry a "Split from ... to keep module cohesion under the 800-line
source limit" header — the split happened, but `cli_ops.spl`'s own copies
of these three `export use` blocks were never deleted afterward).

### Angle B verdict: private-symbol imports are a real, separate trigger — not investigated further here

`use app.cli.arch_check (_str_trim, ...)` and `use app.cli.arch_check
(scan_arch_rules)` (public name) both reproduce the *relint volume* issue
equally — so underscore-prefixed private names are **not** what makes this
particular traversal expensive. Angle B (why private-symbol imports force
"test daemon unavailable; running directly [fallback]" in the first place,
i.e. why the *session daemon* can't serve `arch_check_spec.spl`) is a
distinct question about `app/test_daemon/client.spl` /
`test_runner_main.spl`'s daemon routing, not about the relint traversal —
it was not root-caused in this lane; the fix here removes the *cost* of the
fallback path regardless of why the daemon declines to serve the spec, and
that was sufficient to meet this lane's mission (the daemon path was never
reached in any of the reproductions above; all reproductions used bare
`run`, bypassing the daemon question entirely).

### Fix

`.spl`-only, no Rust rebuild required (the module loader's flatten
behavior was not changed — that's a valid, larger, separate follow-up per
the architectural note above):

- `src/app/io/cli_ops.spl` — removed the three redundant `export use`
  blocks (`_CliCommands.run_commands`, `_CliCommands.handler_commands`,
  `_CliCompile.*`); kept `export cli_handle_compile, cli_env_get, env_set`
  (locally defined in this file, not part of the removed blocks — verified
  `cli_ops.spl`'s own `cli_handle_compile` is a distinct, thin
  `rt_cli_handle_compile` extern wrapper, not the same-named function in
  `handler_commands.spl`).
- `src/app/build/cli_entry.spl` — `use app.io.cli_ops.{cli_native_build,
  cli_run_lint, cli_run_fmt}` → split into `use app.io.cli_compile.
  {cli_native_build}` + `use app.io.cli_commands.{cli_run_lint,
  cli_run_fmt}` (both already re-export the same underlying functions).
- `src/app/cli/_CliMain/main_and_help.spl` — same split: `cli_file_exists`/
  `_cli_eprint` stay on `app.io.cli_ops` (locally defined there);
  `cli_compile`/`cli_native_build` move to `app.io.cli_compile`; the
  ~20 `cli_run_*`/`cli_handle_*` names move to `app.io.cli_commands`. This
  file is the real CLI dispatcher (`build`/`lint`/`fmt`/`native-build`
  etc. all route through it) and genuinely needs the whole compiler either
  way — this edit does not change its own cost, only where it imports the
  same names from.
- `src/app/cli/_CliMain/args_and_os_commands.spl` — `cli_run_lex` moved to
  `app.io.cli_commands`; `cli_get_args` stays on `app.io.cli_ops`.
- Regression guard added: `test/01_unit/app/io/cli_ops_handlers_spec.spl`
  gained an example asserting `cli_ops.spl`'s own source no longer contains
  `export use app.io._CliCompile` / `_CliCommands.run_commands` /
  `_CliCommands.handler_commands`, so this specific regression can't
  silently reappear.

Verified every consumer of the removed names via repo-wide grep for `use
app.io.cli_ops` before and after the edit; the only real consumers of the
heavy names were the three files above (plus `app/io/__init__.spl`, which
already imported `cli_compile`/`cli_run_*` from `app.io.cli_compile`/
`app.io.cli_commands` directly and needed no change).

### `--entry-closure` check (the deleted block's own comment claimed a live purpose — verified, not just assumed)

The removed block's header comment read: `# Exports — re-export CLI
functions so `use app.io.cli_ops.{X}` resolves for --entry-closure` — a
present-tense functional claim, not an obviously-dead comment, and
`--entry-closure` is `native-build`'s own reachable-module BFS
(`_native_build_entry_closure` in
`src/app/io/_CliCompile/compile_targets.spl:424`) — the actual deploy
mechanism. Deleting something that feeds the deploy path to fix a test hang
would be the wrong trade, so this was checked directly rather than assumed
safe:

1. Read `_native_build_entry_closure` and `_nb_module_path_from_use`
   (`compile_targets.spl:314-345`): the BFS walks **textual** `use`/`export
   use` lines only (`_nb_module_path_from_use` explicitly strips both the
   `"use "` and `"export use "` prefixes identically) — it has no notion of
   "export surface"; it just enqueues whatever module path string appears
   in a `use`/`export use` line, wherever that line lives.
2. Since this fix only *edited the `use` statements themselves* in the
   three real consumers (repointing them at `app.io.cli_compile`/
   `app.io.cli_commands` instead of `app.io.cli_ops`), and left
   `cli_compile.spl`'s/`cli_commands.spl`'s own `export use
   app.io._CliCompile.*` lines untouched, the BFS finds the exact same
   destination files — one hop more directly, via `cli_compile.spl`/
   `cli_commands.spl` instead of via `cli_ops.spl`'s now-removed
   redirection.
3. Grepped for any *string-path* reference to the removed re-exports
   outside of `use` statements (build configs, `.sdn` files, docs) that a
   plain `use`-statement grep could miss: `grep -rn "cli_ops\.cli_compile\|
   cli_ops\.cli_native_build\|cli_ops\.cli_run\|cli_ops\.cli_handle"` and
   `grep -rln "cli_ops" --include="*.sdn"` across `src/`, `test/`,
   `scripts/`, `config/` — zero hits.
4. Empirically confirmed with the real mechanism: `SIMPLE_NATIVE_BUILD_TRACE_CLOSURE=1
   ./bin/simple native-build --entry-closure --entry <a file importing
   app.build.cli_entry, post-fix> --source src -o /tmp/entry_probe_out`
   — the closure's own diagnostic trace shows it visiting
   `src/app/io/cli_commands.spl` and `src/app/io/cli_compile.spl`, with
   `cli_compile.spl`'s `export use app.io._CliCompile.compile_opt_and_driver.*`
   / `compile_targets.*` lines appearing in the parsed output — i.e. the
   closure reaches `_CliCompile.*` via the new path, same as it did via the
   old one.

Verdict: `--entry-closure` discovery is unaffected. The deleted comment's
claim was true but the role it described was already redundantly served by
`cli_compile.spl`/`cli_commands.spl` (which the closure BFS treats
identically) — nothing beyond the three `use`-statement repoints was
needed to preserve it.

### Verification

- **Before:** `bin/simple test test/01_unit/app/arch_check_spec.spl` — bounded
  probe at 60s timeout, 169,775 stderr lines, did not complete (matches the
  originally reported >550s/900s+ hang). Load at time of measurement:
  `load average: 12.67, 11.33, 12.12` (32-core box).
- **After:** same command, same binary, same worktree — **14.3-14.8s wall**
  across 3 repeated runs (14.478s, 14.315s, 13.835s for a related spec),
  `Passed: 74, Failed: 0, Duration: 317ms` (internal test-execution clock).
  Load at time of measurement: `load average: 9.17-14.75` (comparable,
  same box, same contention regime as the "before" measurement — not a
  quiet-box artifact).
- Note on the mission's cited seed baseline (`Passed: 74 / Failed: 1`): this
  lane's result is `74/0`. Checked directly — the one historically-failing
  example (`"check-arch is wired in main.spl"`, a `shell("grep -rc
  'check-arch' ...")` check) currently passes on this tip
  (`grep -c "check-arch" src/app/cli/main.spl
  src/app/cli/_CliMain/main_and_help.spl` → 0 + 1 = 1 > 0); this lane's
  edits never touched the string `"check-arch"` anywhere (only import
  lines), so the `74/1` → `74/0` delta is pre-existing drift between this
  tip and the older commit (`3835e717d16`) the original baseline was
  captured on, not a side effect of this fix.
- No stale-cache hazard applies: this fix does not add or touch a cache —
  it removes an unconditional, un-cached transitive dependency. There was
  no cache-key correctness question to verify.
- Regression sample (same binary, same wall-clock ballpark ~13-15s per
  spec — the `test` subcommand's own baseline overhead, unrelated to this
  fix):
  - `test/01_unit/app/io/cli_ops_handlers_spec.spl` — 6/0 (includes the new
    guard example).
  - `test/01_unit/app/io/dir_ops_create_list_spec.spl` — 1/0.
  - `test/01_unit/lib/database/string_interner_numeric_guard_spec.spl` — 1/0.
  - `test/01_unit/lib/audit_log_hash_chain_spec.spl` — 2/5 (5 pre-existing
    failures, confirmed unrelated: this spec explicitly avoids `app.io`
    per its own header comment and imports none of the four files this fix
    touched).
- Import-resolution sanity: standalone probes importing
  `app.build.cli_entry.{handle_build}` and (separately, given it
  legitimately needs the whole compiler either way)
  `app.cli._CliMain.main_and_help.{native_build_backend_supported}` both
  resolved with zero "does not export"/"module error" diagnostics.

### Commit

Committed in `/tmp/wt_relint` (own worktree per this lane's mission — not
pushed; a separate review+landing lane handles that).
