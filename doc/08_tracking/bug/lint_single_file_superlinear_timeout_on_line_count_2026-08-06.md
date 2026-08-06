# Bug: `bin/simple lint <file>` times out (>300s) on files above ~150-300 lines, purely as a function of line count

**ID:** lint_single_file_superlinear_timeout_on_line_count_2026-08-06
**Severity:** P1 — makes `bin/simple lint` unusable on any file over a few hundred
lines
**Status:** Localized to the shared parse+decl-collection prefix of
`run_lint_file`; exact quadratic site NOT pinned; no working fix landed
**Reported:** 2026-08-06

---

## Summary

Two independent lanes this session hit `bin/simple lint <file>` never completing
(300-590s+) on:

- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl`
  (2613 lines, 142,853 bytes, 73 top-level `fn`/`me` signatures, only 2 `use`
  imports)
- `src/lib/gc_async_mut/gpu/browser_engine/containment.spl`

A standing project note ("`bin/simple lint` scans the whole repo tree regardless
of the file argument") was floated as the explanation. **That theory is false**
— see "Ruled out" below. The real mechanism is a severe superlinear (looks
worse than quadratic) blow-up in wall-clock time as a function of the target
file's own line/declaration count, reproducible on **purely synthetic,
content-free** input. This is NOT the same defect as
`doc/08_tracking/bug/ast_env_var_quadratic_parse_2026-06-13.md`, even though it
has the same shape and that doc's proposed fix was tried and does not help —
see "Distinct from the known env-var quadratic bug" below.

---

## Ruled out: "lint scans the whole repo tree"

Read, not guessed:

- `src/app/io/cli_lint_commands.spl:143-165` (`run_lint_command`) — a non-directory
  target is pushed into `lint_files` as exactly one entry; `discover_spl_files`
  (repo/dir walk) is only called when the target `is_dir(target)`. A file
  target never triggers directory discovery.
- `src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl:35-38`
  (`lint_cli_source`) parses only the given file's own `content` string via
  `parse_module_silent_checked(content, path)` — no transitive import
  resolution.
- The slow target file has exactly 2 `use` imports, both within the same
  directory (`layout_table`, `containment`).

**Verdict: scoping is correct.** A single-file target lints exactly that file.
The "whole repo" folklore should be retired.

---

## Empirical timing (synthetic reproducer, content-independent)

Generator (write with `Write`, not `python3` — the ad hoc python was scratch-only,
never committed, kept here as prose since repo rules forbid Python in
committed artifacts):

> For `n` in {50, 150, 300, 1300}: write `n` repetitions of
> ```
> fn synthetic_fn_<i>(a: i64) -> i64:
>     a + <i>
> ```
> to a `.spl` file (no imports, no classes, no strings — content-minimal).

| File | Lines | Bytes | `bin/simple lint` result |
|---|---|---|---|
| 3-line trivial (`fn main(): print "hi"`) | 3 | ~30 | 3.3s, completes |
| `syn_50.spl` (50 fns) | 100 | ~2.5K | **20.1s**, completes |
| `syn_150.spl` (150 fns) | 300 | ~7.5K | times out, >40s |
| `syn_300.spl` (300 fns) | 600 | ~15K | times out, >60s |
| `syn_1300` (1300 fns) | 2600 | 62,780 | times out, >60s |
| real target file (73 fns, real content) | 2613 | 142,853 | times out, >100s (originally reported 300-590s) |
| real target file, half (1300 lines) | 1300 | 69,532 | times out, >90s |
| real target file, two giant 7062-char lines truncated to one-liners | 2613 | smaller | still times out, >60s (giant lines are NOT the driver) |

Reference for comparison: `bin/simple fmt --check` on the **same** `syn_300.spl`
(600 lines) — which also fully parses the file — completes in **21.0s**. Slow,
but not a hang. `lint` on the identical file, with every one of its own lint
*checks* stubbed out (see below), still does not finish in 60s. The
lint-specific delta over `fmt --check` is real and is not explained by parsing
alone.

The 100→20s single data point against fmt's 600→21s is not enough to fit an
exact exponent, but the shape (a 3-line file in 3.3s, a 100-line file in 20s, a
300-line file not finishing in 60s) is consistent with the superlinear/quadratic
family already seen elsewhere in this codebase (`.claude/memory` "Measurement
traps" and "Compiler/language defects" quadratic entries) and matches the
*shape* — though not, per the section below, the *site* — of the tracked
`ast_env_var_quadratic_parse_2026-06-13` bug.

---

## Localization performed (behavioral bisection, not print-probes)

**Important methodological note for whoever picks this up:** `eprint` inside
this call graph is **not reliable ordering evidence**. In one run, `before
check_all_rules call` and `after check_all_rules` both printed while the eprint
that is the literal first statement inside `check_all_rules` never printed —
impossible under honest ordered output. Every earlier working hypothesis this
session built purely on "probe X never printed" (interpreter fallback at the
`check_all_rules` call boundary, hang inside
`_collect_duplicate_typed_arg_signatures`) was retracted for exactly this
reason. **Only wall-clock timing on a stubbed-out call graph is trustworthy
here** — verified by editing the actual `.spl` source (not env vars, not
flags) to `return []`/skip a call, then timing.

Behavioral bisection performed on `syn_300.spl` (600 lines), each stub reverted
immediately after measurement (`git diff --stat` confirmed byte-identical to
`main` after every revert — see "Housekeeping"):

1. **`check_all_rules()` (the 24-rule EasyFix registry, `registry.spl`) stubbed
   to return `[]` entirely** — still times out at 60s. Not the driver.
2. **`Linter.lint_source`'s per-line `check_line` loop AND all 17 whole-content
   `self.check_*` calls stubbed out**, `check_all_rules` also still stubbed —
   still times out at 60s. Not the driver.
3. **All 6 decl-based checks in `entry_and_fixes.spl`
   (`check_argument_count`, `check_collection_patterns`, `check_stub_impl`,
   `check_star_export_file`, `check_wide_public_file`,
   `check_option_me_call_source`) also stubbed to empty**, on top of 1 and 2 —
   **still times out at 60s.**

At this point every lint *check* function reachable from `run_lint_file` is a
no-op; the only work left in the call graph is:
`parse_module_silent_checked(content, path)` (the parse gate) →
`resolve_lint_config` → `module_get_decls()` → `content.split("\n")`.

`fmt --check` on the identical file (which also fully parses) completes in
21s. The stubbed-lint path, doing strictly less work than `fmt --check` plus
one call to `module_get_decls()`, still does not finish in 60s. This points at
either the parse step behaving differently under the lint entry point than
under the fmt entry point, or `module_get_decls()` / its `module_decl_at()`
backing store.

**Not fully pinned within this session's effort budget.** The next step is to
stub `module_get_decls()` itself (return `[]` without calling
`ast_module_decl_count_get()`/`module_decl_at()`) and re-time; if that flips it
to fast, the culprit is confirmed as `module_decl_at()`'s environ-scan fallback
in `src/compiler/10.frontend/core/_Ast/module_state.spl:439-449`; if not, the
parse gate itself (`parse_module_silent_checked`) needs the same bisection
treatment, or the divergence from `fmt --check`'s 21s needs to be explained
directly (they should call largely the same parser).

---

## Distinct from the known env-var quadratic bug — tried and does NOT fix this

`doc/08_tracking/bug/ast_env_var_quadratic_parse_2026-06-13.md` documents a real,
already-localized O(N²) defect: AST node reads/writes falling back to
`rt_env_get`/`rt_env_set` (linear `environ[]` scan) instead of the arena
arrays, gated by `SIMPLE_NATIVE_ARENA_DECLS`. Given the matching shape (52s/146s/
timeout at N=100/200/400 in that doc vs. this session's 20s/timeout/timeout at
n=50/150/300), this looked like the same bug. It is not, or at least setting the
documented flag does not reproduce that doc's claimed fix here:

- `src/compiler/10.frontend/core/_Ast/decl_nodes.spl:141-166` — a 2026-07-24
  follow-up already made **arena-preferred the default** for per-decl-field
  reads/writes (`ast_decl_arena_default()` returns 1 unless
  `SIMPLE_BOOTSTRAP==1`, which ordinary `bin/simple lint` never sets). So the
  specific mechanism the 2026-06-13 doc fixes for is **already off by default**
  in a plain lint run — no flag needed.
- `src/compiler/10.frontend/core/_Ast/module_state.spl:439-449`
  (`module_decl_at`) is a **separate, inconsistent** accessor that was not
  updated to match: it hardcodes `rt_env_get_i64("SIMPLE_NATIVE_ARENA_DECLS", 0)`
  — default **0** (slow path), not `ast_decl_arena_default()`'s default of 1.
  This looked like a promising, narrow, bounded fix target.
- **Tried and falsified, twice:**
  1. In-process fix: `src/app/io/cli_lint_commands.spl`'s `run_lint_command`
     wrapped the file-processing loop in
     `env_set("SIMPLE_NATIVE_ARENA_DECLS", "1")` / restore-after, mirroring the
     exact precedent already in `src/app/io/_CliCompile/compile_targets.spl:1114`
     (which does this around native-build compiles). **No effect** — `syn_300.spl`
     still timed out at 60s with the flag set from inside the running process.
  2. Exogenous fix, to rule out an in-process JIT-caching/staleness explanation:
     `SIMPLE_NATIVE_ARENA_DECLS=1 bin/simple lint syn_300.spl` (flag set in the
     real OS process environment from the shell, before the process even
     starts). **Also no effect** — still timed out at 40s (tested with a
     shorter budget).

Both attempts were reverted; `git diff --stat` against `main` is empty for
every file touched this session (see Housekeeping). **The
`SIMPLE_NATIVE_ARENA_DECLS` flag is not the lever for this specific hang.**
Either `module_decl_at` isn't actually the bottleneck (consistent with the
bisection above, which never got to isolate it cleanly since stubbing its only
caller, `module_get_decls`'s 6 consumers, didn't help either — the parse gate
itself was never separately stubbed), or there is a second, distinct
quadratic site this session did not reach.

---

## What a future session should do

1. **Trust timing, not `eprint` ordering**, in this call graph — see the
   methodological note above.
2. Bisect `parse_module_silent_checked` vs `module_get_decls()` directly (stub
   each to a constant, one at a time, and re-time `syn_300.spl`) to finish the
   localization this session left at "somewhere in the parse+decl-collection
   prefix, not in any of the ~44 individual lint check functions."
3. If it lands back in `_Ast`/`module_state.spl`, treat as a sibling of
   `ast_env_var_quadratic_parse_2026-06-13` (same file family, same author
   intent) rather than reopening that doc — the earlier fix already shipped
   for the sibling accessor family; this is either a second un-migrated
   accessor or a genuinely different mechanism.
4. Confirm on the real target file
   (`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl`)
   once a fix candidate exists — the synthetic reproducer is enough to
   iterate cheaply, but the real file (73 fns, 2613 lines, 142KB) is the actual
   user-facing case and should complete well under 120s post-fix with byte-
   identical lint findings to a (very patient) pre-fix run.

---

## Housekeeping

All instrumentation (eprint probes) and both attempted fixes were reverted.
Verified with `git diff --stat` against `main` for every file touched this
session — empty in every case:
`src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl`,
`src/compiler/90.tools/lint/_LintMain/lint_checks.spl`,
`src/compiler/90.tools/fix/rules/registry.spl`,
`src/compiler/90.tools/fix/rules/impl_/lint_spec.spl`,
`src/compiler/90.tools/fix/rules/impl_/lint_code.spl`,
`src/app/io/cli_lint_commands.spl`. No code change shipped from this
investigation; this doc is the only artifact.
