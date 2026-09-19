# Lint pipeline: COLL census, cost attribution, and the redundant-parse fix (2026-09-19)

Lane D1. Goal: use the repo's own COLL lint rules to find and fix quadratic /
non-dataframe collection code in the pure-Simple compiler, interpreter and
loader, and prove the speedup with measurements.

**Headline: 2.32x on the canonical slow lint (median 53.19s -> 22.93s), by
removing two of three redundant full parses of the same buffer. The COLL rules
did NOT locate the hot spot — timing probes did. Every COLL finding in the
executed hot path is over a collection bounded small enough to measure as 0ms;
the numbers and the bound for each are in § Left alone.**

## Environment (recorded for every run)

| item | value |
|---|---|
| `readlink -f bin/simple` | `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` |
| binary size / mtime | 51607912 bytes, 2026-09-19 09:09:30 +0900 |
| `bin/simple --version` | `Simple Language v1.0.0-beta.12` — **the Rust bootstrap seed**; it prints its own "bootstrap seed only" warning. No pure-Simple full CLI is deployed on this host. |
| binary stability | `stat` re-read after the last of the nine A/B runs: unchanged, same size and mtime. The binary was identical for all nine runs. |
| host | aarch64, Linux 6.17.0-1032-nvidia, shared box, load 10-25 during the session |
| base commit | `7c875a81067`, branch `work/df-apply` |

The seed runs the lint pipeline as **interpreted pure Simple**: an strace of one
`bin/simple lint` opens 130 unique `src/compiler/**.spl` and 85 `src/lib/**.spl`
files, and the run reports
`[jit-fallback] ... whole module dropped to the interpreter` (pre-existing, cause
`CodeLine.code` field inference in `src/app/cli/lint_entry.spl`; see
`doc/08_tracking/bug/lint_dejits_whole_program_span_struct_collision_2026-08-18.md`).
So `lint` of a large real compiler file is a real pure-Simple compiler workload,
and it is the workload the repo itself gates
(`scripts/check/check-lint-cost-budget.shs`).

## Step 1 — COLL census over the EXECUTED hot path

Rather than sweeping `src/compiler/` blind, the file set was taken from the
strace above: the 130 compiler + 85 stdlib `.spl` files the lint workload
actually executes (`10.frontend` parser 84, `90.tools/lint` 131 opens,
`35.semantics` 56, `00.common` 16). All 215 were linted individually
(`xargs -P 6`, 4m19s wall, ~2.4s/file on this binary — note the
`.claude/rules/commands.md` "~12s startup, superlinear" table predates this
binary and over-predicts it by ~5x).

**206 COLL findings, by rule:**

| rule | count | what it flags |
|---|---|---|
| COLL008 | 175 | unbounded global `.push()` with no reset/capacity guard |
| COLL002 | 13 | `.contains()` on an array inside a loop |
| COLL006 | 9 | string concat in a loop |
| COLL015 | 4 | nested loops compared by `==` (accidental cartesian product) |
| COLL001 | 3 | array concat in a loop |
| COLL007 | 2 | array rebuild to drop the last element |

Top files by finding count: `10.frontend/core/_Ast/decl_nodes.spl` (64),
`10.frontend/core/types.spl` (50), `10.frontend/core/_AstExpr/nodes.spl` (25),
`10.frontend/core/ast_stmt.spl` (13) — all COLL008 on the AST arena globals.

## Step 2 — where the time actually goes

Temporary `rt_time_monotonic_ns()` probes in `lint_cli_source`,
`Linter.lint_source`, `run_static_lint_rule_table` and
`check_param_object_rules` (all reverted; not in the commit). One run,
1619-line prefix of `src/compiler/50.mir/hwir/zca_rows.spl`, load ~10, ~81s wall:

| phase | ms |
|---|---|
| `lint_source_for_parsed_append` (text lints) | **29932** |
| `parse_module_silent_checked` (AST rules' own parse) | **12987** |
| `lint_source_location_index` | 229 |
| `check_collection_patterns` (COLL rules themselves) | 86 |
| `check_stub_impl` | 4 |
| `content.split`, ARG, REQC, W0406, wide-public, OPTME | 0 |

Inside the text lints:

| sub-phase | ms |
|---|---|
| `check_static_lint_rules` | **24296** |
| `check_ui_raw_theme_name` | 1020 |
| `check_all_rules` (shared EasyFix) | 712 |
| `check_ui_raw_widget_kind` | 328 |
| `check_ui_raw_variant` | 247 |
| `check_raw_rt_access_spl` | 221 |
| `check_primitive_api` | 10 |
| all 11 others (feature-tracking, spipe, theme, stale-md, llvm, dyn-cap, wm-lane, gpu-2d, script-required, filter) | 0 |

Inside `run_static_lint_rule_table` (15 rules):

| rule | ms |
|---|---|
| `param_object` | **24267** |
| `silent_default` | 12 |
| the other 13 (`accessor_parent_name`, `bare_primitive_internal`, `const_ref_default`, `cow_alias_hotpath`, `leading_operator`, `linear_scan_in_loop`, `module_init_literal`, `nonexistent_type`, `os_freestanding`, `param_tag`, `raw_sffi`, `riscv_debuggability`, `unwrapped_foreign_resource`) | 0 |

Inside `check_param_object_rules`:

| step | ms |
|---|---|
| `param_object_schemas_from_source` (parse #1) | **12824** (`structs=0`) |
| struct-pair loop (the COLL015 site) | **0** |
| second `parse_module_silent_checked` (parse #2) | **11766** |
| `_param_env_decl` walk | 600 |

**Diagnosis: linting one file parsed the same buffer three times** — twice in
`check_param_object_rules` (once for the struct projection, once for the env
walk) and once more in `lint_cli_source` for the AST rule loops. A grep of the
whole lint path confirms exactly three `parse_module_silent_checked` call sites
and no others (`90.tools/lint`, `35.semantics/lint`, `90.tools/fix` all checked;
`std.tooling.easy_fix`'s `check_all_rules`, which runs between parse #2 and
parse #3, contains no `parse_module`/`ast_reset` at all).

The generation-bump chain the memo rests on is **verified, not assumed**:
`parse_module_silent_checked` -> `_parse_module_with_diagnostics` ->
`parser_init_with_path` -> `ast_reset()` (`10.frontend/core/parser.spl:273`) ->
`ast_generation_bump()` (`_AstExpr/nodes.spl:392`). A widened grep for
`parse_module_file` / `parse_module(` / `parse_module_silent` / `ast_reset(`
across `src/app/cli/lint_entry.spl`, `src/app/io/cli_lint_commands.spl`,
`src/app/lint/`, `src/compiler/90.tools/`, `src/compiler/35.semantics/` and
`src/lib/nogc_sync_mut/tooling/` finds **no** further parse site after this
change — in particular no `parse_module_file`, the one entry that adds decls to
the arena WITHOUT resetting it (and therefore without bumping the generation).

## Step 3 — the changes

**Fix A — one parse per rule** (`param_object_rules.spl`). Split the projection
off the parse: new `param_object_schemas_from_parsed_module()` reads the module
the arena already holds; `check_param_object_rules` parses once at the top and
the env walk reuses it. `param_object_schemas_from_source` is kept — it still
has a caller, `scripts/check/check_param_object_evolution.spl`.

**Fix B — one parse per lint of a file** (new
`src/compiler/90.tools/lint/lint_parse_memo.spl`, 41 lines).
`lint_parse_module_memo(source, path)` wraps `parse_module_silent_checked` and
skips it when the arena already holds that exact `(path, source)` at that exact
`ast_generation()` — the same validity triple `lint_parsed_revision` already
uses. `ast_reset()` bumps the generation **before** clearing the arena, so any
other parse between two calls invalidates the memo and the next call re-parses;
a miss costs one text comparison and can never serve decls the arena no longer
holds. Both remaining call sites (`check_param_object_rules`,
`lint_cli_source`) go through it. 3 parses -> 1.

This is the design doc's principle (`adaptive_collections_typed_query_design.md`
§10: index/reuse instead of recompute) applied at module granularity rather than
row granularity. **It is not a COLL rule, and no COLL rule can see it.**

## Step 4 — before/after, interleaved

Workload: `bin/simple lint src/compiler/50.mir/hwir/zca_rows.spl` (1901 lines,
real compiler file, the file `doc/08_tracking/bug/lint_timeout_hwir_zca_rows_2026-08-17.md`
is about). **Arms are interleaved round-robin, not blocked**, because a first
blocked baseline drifted 92.99 -> 101.78 -> 107.39s purely on host load
(14.24 -> 22.45 -> 24.75) and was discarded as non-comparable. `/usr/bin/time -v`
per run; the swap between arms rewrites only the two touched `.spl` files (the
stdlib and compiler are read as source every run, so no build step is involved).

| arm | round 1 | round 2 | round 3 | min | median | median RSS |
|---|---|---|---|---|---|---|
| base (vB) | 55.48s (load 12.94) | 51.06s (11.93) | 53.19s (10.57) | 51.06s | **53.19s** | 664408 kB |
| +Fix A (vA) | 40.40s (11.95) | 34.62s (10.24) | 46.02s (10.53) | 34.62s | **40.40s** | 649124 kB |
| +Fix A+B (vAB) | 21.59s (12.08) | 22.93s (10.49) | 39.96s (15.51) | 21.59s | **22.93s** | 620252 kB |

| comparison | median | min | RSS |
|---|---|---|---|
| base -> A | 1.32x | 1.47x | -2.3% |
| A -> A+B | 1.76x | 1.60x | -4.4% |
| **base -> A+B** | **2.32x** | **2.36x** | **-6.6%** |

Median, not mean: the vAB round-3 outlier (39.96s) was taken at load 15.51, the
highest of the nine runs.

`sh scripts/check/check-lint-cost-budget.shs` after the change:
`PASS — 1 fixture(s) checked, lint completed in 1s of a 240s budget (load=9.50,
concurrent simple=6)`, selftest 4/4.

## Step 5 — behaviour identity

- **Findings identity:** lint findings collected for 9 real files
  (`lint_rule_api.spl`, `resource_families.spl`, `dangerous_keywords.spl`,
  `mc_exceptions.spl`, `linear_scan_in_loop.spl`, `frame.spl`,
  `collection_profile.spl`, `driver_public_header_parse.spl`, plus
  `param_object_rules.spl` itself) and a deliberately unparseable fixture, base
  vs A+B: **byte-identical**, excluding the one row that is the edited file's own
  text. The PARSE001 path is exercised and identical down to the reason text
  (`error[PARSE001]: NOT LINTED: ... (expected parameter name)` at `2:1`), which
  proves `parser_first_error_get()` still works through the memo.
- **Spec identity:** all 74 specs in `test/01_unit/compiler/lint/` run one
  positional per invocation, base vs A+B: **identical outcomes, 37 PASS /
  37 FAIL**. The 37 failures are **pre-existing at `7c875a81067`** and unchanged
  by this work (they include `param_object_lint_spec.spl`, 5/6, failing example
  "accepts an append-only parameter object with hdr first and ext last" —
  verified red on the unmodified tree before any edit).
- **New spec:** `test/01_unit/compiler/lint/lint_parse_memo_spec.spl`, 2 examples,
  green. Mutation-checked: deleting the `_LINT_PARSE_SOURCE == source` term from
  the memo key turns **both** examples red, so it is not vacuous. Not mirrored
  into `test/unit/compiler/lint/` — that tree carries 14 of the 74 specs, so the
  new file creates no divergence pair.
- `sh scripts/check/check-pure-simple-lint-runnable.shs`:
  `PASS - 2 fixture(s) linted, pure-Simple lint_entry.spl executed and its
  findings discriminate (bin/simple)`.
- `bin/simple lint` on all three touched files: `lint_parse_memo.spl` and
  `param_object_rules.spl` clean; `entry_and_fixes.spl` reports only its
  pre-existing `unnamed_duplicate_typed_args` warnings. (`lint_parse_module_memo`
  is deliberately not `pub` — as `pub` it drew a new `primitive_api` warning for
  returning a bare `bool`, and cross-module `use` does not require `pub` here.)

## Left alone — with the measurement that says why

Every row below is a COLL finding in the executed hot path that was
**deliberately not changed**. "A change with no measurable win gets reverted,
not kept", so none was made.

| finding | why left alone (measured) |
|---|---|
| COLL015 `check_param_object_rules` struct-pair loop (`for item in structs: for previous in structs:`) — a genuine O(n²) and the textbook `index_by` candidate | Measured **0 ms** (`PROBE4 struct_pairs`). `n` is structs+classes in ONE file: `structs=0` for `zca_rows.spl`, and the repo-wide maximum over every `src/**/*.spl` is **45** (next 40, 35). Worst case is ~2025 `_version_base` calls against a 12.8s parse. A Dict index here buys nothing measurable. |
| COLL006 `10.frontend/core/types.spl:59` `int_to_str` string concat in loop | Loop is `for k in 0..20` with a `break` at `v == 0` — bounded at 20 concatenations of a ≤20-char string, independent of program size. |
| COLL002 `10.frontend/core/dangerous_keywords.spl:28` `source_may_contain_dangerous_keyword` | `DANGEROUS_KEYWORDS` holds **5** elements, and the function has exactly one caller (`35.semantics/lint/required_comment.spl:32`) invoked **once per file**, not per declaration. 5 substring scans per file. |
| COLL008 × 175, mostly `_Ast/decl_nodes.spl` (64), `core/types.spl` (50), `_AstExpr/nodes.spl` (25) | These are the AST **arenas**. Unbounded growth during a parse is their purpose; they are cleared by `ast_reset()`, which the rule cannot see. Converting them is an arena redesign, not a collection fix. |
| COLL002 in `35.semantics/lint/linear_scan_in_loop.spl:68`, `riscv_rtl_debuggability_lint.spl:13`, `_SimdOpportunityLint/loop_analysis.spl:152`, and COLL007 at `linear_scan_in_loop.spl:97` | Their whole rules measure **0 ms** each in the per-rule probe (`linear_scan_in_loop`, `riscv_debuggability`, and the rest of the static table). |
| COLL002 in `90.tools/lint/_LintMain/{gpu_2d_perf,os_freestanding,wm_lane_boundary}_lints.spl` and `entry_and_fixes.spl:521` | `check_gpu_2d_perf` / `check_wm_lane_boundary` measured **0 ms** — they are opt-in and short-circuit on one dict probe when off. `entry_and_fixes.spl:521` is in the COLL002 Certain-fix textual scan, inside the 0 ms tail. |
| COLL015 `10.frontend/core/parser_decls_use.spl:759` | The nested loops are over `parse_type_params()` results — generic parameters of one `impl` head, single digits. |
| COLL001/COLL006/COLL002 in `src/lib/nogc_async_mut/env/*`, `nogc_sync_mut/path.spl`, `common/crypto/types.spl`, `common/binary_inspect.spl`, `common/ui/native_scalar_text.spl`, `nogc_sync_mut/ui/theme_package.spl` | Loaded by the lint process but not executed on this workload: the phases that would call them (`check_theme_package`, `check_stale_md_diagrams`, `check_llvm_backend_type_safety`, `check_dynamic_capability_acquire_spl`) all measure **0 ms**. |

## Flat / negative results, with the reason

| workload | result | why |
|---|---|---|
| `bin/simple test --no-session-daemon <spec>` | **flat, no win possible** | Not a "small collection" story — the touched code is not on that path at all. strace of `bin/simple test test/01_unit/compiler/lint/collection_frame_rules_spec.spl` opens **19** unique `src/compiler/**.spl` files and **zero** under `src/compiler/90.tools/**`. The spec run exercises `10.frontend/core/{ast,ast_expr,ast_stmt,ast_types,types,call_graph,closure_analysis,...}`, `00.common/assurance/*` and `80.driver/driver_mcdc_report_gate.spl`, never the linter. Measuring a 3x3 there would measure noise. |
| COLL015 struct-pair -> Dict index in `check_param_object_rules` | **not implemented** | Asymptotically better and idiomatic, but the site measures 0 ms with a repo-wide worst case of n=45 (above). Implementing it would have been a diff with no measurable win. |
| first, blocked baseline (3 runs base, then 3 runs after) | **discarded** | Host load rose 14.24 -> 22.45 -> 24.75 across the three baseline runs (92.99 / 101.78 / 107.39s), which is larger than the effect being measured. Replaced with the interleaved design above. All nine interleaved runs sat at load 10.2-15.5. |

## Open, not fixed here

1. The de-JIT is still live: `lint` drops the whole program to the interpreter
   because of `CodeLine.code` field inference in `src/app/cli/lint_entry.spl`.
   Fixing it multiplies every number above.
2. One parse of a 1901-line file still costs ~12s interpreted and is now ~55% of
   the remaining lint wall time. That is the next target, and it is a parser
   problem, not a collection problem.
3. The 37 pre-existing failures in `test/01_unit/compiler/lint/` at
   `7c875a81067` are untouched and unexplained by this lane.

## Push-gate note (recorded, per .claude/rules/vcs.md)

`sh scripts/check/check-test-tree-divergence-delta.shs 7c875a81067 HEAD` ->
`PASS — 3206 pre-existing offender(s), 0 introduced by this range`. The base
itself is RED (`FAIL — 3922 diverged vs 965 baselined (3066 new, 109
fixed-but-still-baselined); 32 mirror-only (31 unallowlisted)`) — entirely
pre-existing at `7c875a81067` and not touched by this lane. The guard saved the
pre-existing offender list to `/tmp/test_tree_divergence_preexisting.txt`; the
scoped-delta escape requires that list be recorded before landing, which this
section does.

**Not done in this lane:** the `.claude/rules/vcs.md` § "LLM wiki before commit"
refresh of `doc/00_llm_process/{feature_expert,layer_expert}/**/skill.md`. Flagged
rather than silently skipped.
