# `simple lint` runs the entire pure-Simple linter in the tree-walking interpreter (two stacked de-JIT causes)

- Date: 2026-08-18
- Status: **OPEN — root cause located and reproduced; fix not landed**
- Supersedes the "superlinearity not located" section of
  `doc/08_tracking/bug/lint_timeout_hwir_zca_rows_2026-08-17.md`.
- Binary identity for every number below:
  `bin/simple -> bin/release/x86_64-unknown-linux-gnu/simple`,
  size `59620392`, mtime `2026-08-18 01:08:42 +0000`. Shared box,
  load average recorded per measurement. **User CPU**, not wall clock.

## What was actually wrong

A prior lane attributed ~98% of `bin/simple lint` cost to `ast:parse_module`
(`parse_module_silent_checked`, `src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl:71`)
and concluded the pure-Simple parser had a superlinear algorithmic defect. The
attribution to the parser is correct. **The conclusion that the parser contains
the defect is not supported.** The parser is slow because it is being
*interpreted*, and it is being interpreted for two independent, stacked,
mechanical reasons.

### Cause 1 — lint is pinned to the interpreter by a source text-grep

`simple lint` dispatches to `src/app/cli/lint_entry.spl`
(`src/compiler_rust/driver/src/main.rs:1355`). That file's first import is:

```
use std.cli.cli_util (get_cli_args)
```

`should_prefer_interpreter_for_source` (`src/compiler_rust/driver/src/exec_core.rs:1412`)
calls `source_uses_cli_args`, which greps the ENTRY FILE'S TEXT for
`get_cli_args` / `rt_cli_get_args` / `sys_get_args` / `rt_get_args` / `std.cli`
(lines 1431-1435). `lint_entry.spl` matches on two of the five. The JIT is
therefore never even attempted for lint: the whole program — including the
entire pure-Simple compiler frontend it imports — executes in the seed's
tree-walking interpreter.

The escape hatch is any value of `SIMPLE_EXECUTION_MODE` (line 1416).

### Cause 2 — with the JIT requested, the whole module still de-JITs on a duplicate `Span`

`SIMPLE_EXECUTION_MODE=jit bin/simple lint <fixture>` gets past cause 1 and then
prints:

```
[jit-fallback] HIR lowering error: Cannot infer field type: struct 'Span' field
'end_pos' (declared fields: start, end, line, col, file, length)
[in src/app/cli/lint_entry.spl]: whole module dropped to the interpreter
(expect ~100-1000x slowdown).
```

Two different structs are both named `Span` in the co-compiled graph:

| file | fields |
|---|---|
| `src/compiler/00.common/diagnostics/span.spl:7` | `start, end, line, col, file, length` |
| `src/compiler/10.frontend/core/lexer_types.spl:12` | `start, end_pos, line, col` |

HIR lowering resolves struct names globally by bare name, picks the diagnostics
variant, and fails on the lexer's `end_pos`. This is a *known* defect class in
this repo — the `GlyphBitmap`/`gbm_*` case — and the remedy already exists:
`collect_duplicate_struct_defs` (`src/compiler_rust/compiler/src/pipeline/module_loader.rs:1321`)
feeds the lowerer's duplicate-variant consensus fallback. It is **gated OFF by
default** behind `SIMPLE_JIT_DUP_STRUCT_FEED`
(`src/compiler_rust/driver/src/exec_core.rs:1056-1060`) because it caused a
render divergence on widget-heavy graphs on 2026-08-11.

## Measurements

Fixture: first 49 lines of `src/compiler/50.mir/hwir/zca_rows.spl`
(`fix49.spl`), the same shape the prior lane used. All three arms produced the
identical verdict `Lint passed: all files clean`, rc 0.

| arm | user CPU | wall | max RSS | jit-fallback lines | load |
|---|---|---|---|---|---|
| default (`bin/simple lint`) | **39.23s** | 47.02s | 317 MB | n/a (JIT never attempted) | 30-42 |
| `SIMPLE_EXECUTION_MODE=jit` | **23.39s** | 28.39s | 333 MB | 1 (`Span`/`end_pos`) | 21-30 |
| `SIMPLE_EXECUTION_MODE=jit SIMPLE_JIT_DUP_STRUCT_FEED=1` | **52.57s** | 62.04s | 399 MB | 0 through HIR lowering | 21-26 |

At 49 lines the dup-struct-feed arm is the SLOWEST of the three: unblocking the
whole-graph JIT means actually compiling the whole lint import graph, and that
fixed cost (~30s) exceeds what it saves on a tiny file. Three functions still
fell back (`[CODEGEN-STUB-FALLBACK]` on `path_separator`, `search_path`,
`path_find_all`, all `GlobalLoad: unresolved identifier`), so even this arm is
not fully JIT'd.

### The larger fixture, where run time should dominate

Fixture: first 182 lines of `zca_rows.spl` — the same 2-function prefix the
prior lane timed at 210s wall. Run A-B-A back-to-back in one serial batch to
control for load drift. All arms verdict `Lint passed: all files clean`, rc 0.

| arm | user CPU | load |
|---|---|---|
| A1 default | **222.95s** | 19-23 |
| B `SIMPLE_EXECUTION_MODE=jit SIMPLE_JIT_DUP_STRUCT_FEED=1` | **181.37s** | 20-26 |
| A2 default (repeat control) | not completed before this lane ended; load had risen to 36 |

**This is the important negative result.** Removing the `Span` de-JIT blocker
buys **1.23x**, not the 100-1000x the fallback warning advertises. So while the
de-JIT is real, reproducible, and worth fixing, it is **not by itself** the
whole explanation for lint's cost, and anyone landing the `Span` rename should
expect ~20%, not two orders of magnitude. The remaining cost is still
interpretation — the stub fallbacks above show the graph does not fully JIT even
when HIR lowering succeeds — but locating *which* functions stay interpreted is
follow-up work this lane did not do.

### Whole-lint growth, for the record

| lines | default user CPU |
|---|---|
| 49 | 39.23s |
| 182 | 222.95s |

3.71x lines -> 5.68x cost, exponent **1.33** (1.56 if the ~12s fixed startup is
subtracted from both). So whole-`lint` IS mildly superlinear even though the
lexer alone is not — the superlinear part lives in the parser or the AST-rule
tier, not the tokenizer. That narrowing is the honest state of the search.

## The parser itself is LINEAR, not superlinear

Measured directly, in-process, on increasing prefixes of `zca_rows.spl`, by
calling `lex_tokenize_all` repeatedly inside one process (so the ~12s startup is
paid once and cannot contaminate the curve):

| lines | bytes | tokens | time |
|---|---|---|---|
| 25 | 1480 | 175 | 4.05s |
| 50 | 2795 | 428 | 8.23s |
| 100 | 6652 | 1206 | 25.54s |

428 -> 1206 tokens is 2.82x for 3.10x time: exponent **1.09**. The lexer is
essentially linear in token count. What it is, is **~21 ms per token**, which is
the interpreter penalty and nothing else.

This does not by itself prove the *parser* (as opposed to the lexer) is linear —
that arm was cut short — but it removes the lexer, which the prior lane's
"content complexity" framing implicated, from the list of superlinear suspects.

## Verdict: dominated by a constant factor; a mild superlinear term survives

The dominant term is a **constant factor from executing the compiler frontend
interpreted** — ~21 ms per token, with the lexer itself provably linear. That is
not something rescan-hunting or pass restructuring inside the parser will touch.

But the honest picture is two-part, and the second part is not dismissed:
whole-`lint` still shows an exponent of ~1.33 across 49 -> 182 lines while the
lexer shows 1.09, so **something above the tokenizer does grow superlinearly**.
It is a secondary term, not the dominant one, and it has not been localised.
Do not close the superlinearity question; do not lead with it either.

## Fix options, in order of preference

**Expected payoff, stated up front so nobody over-invests: 1.23x, measured.**
Not 100x. Options 1 and 3 both attack the same de-JIT and should be sized
accordingly.

1. **Rename the frontend `Span`** (`src/compiler/10.frontend/core/lexer_types.spl`)
   to a unique name. This is the sanctioned remedy for this collision class in
   this repo. Blast radius measured: ~10 `src/` files, ~90 `Span` occurrences;
   two of them (`10.frontend/parser_types.spl`, `30.types/dim_constraints.spl`)
   import BOTH `Span` types and must be edited by hand, not by `sed`. Needs a
   full test pass — not attempted here under a live 20 GB bootstrap.
2. **Narrow `source_uses_cli_args`.** Grepping an entry file's raw text for five
   substrings is a blunt instrument that costs the single most-used tool in the
   repo a 100-1000x penalty. It should at minimum not fire for `lint_entry.spl`.
   Rust-side; needs a seed rebuild.
3. **Un-gate `SIMPLE_JIT_DUP_STRUCT_FEED` for non-graphics lanes.** The
   2026-08-11 divergence was on widget-heavy graphs; lint has no widgets.

## Do not

Do not "optimise" the parser's pass structure on the strength of the earlier
superlinear framing. Do not delete the `LINTPROF` level-gated timers
(`lint_prof_now`/`lint_prof_mark`, `src/compiler/90.tools/lint/_LintMain/lint_checks.spl:59`);
they are default-off and free, and they are what localised this.
