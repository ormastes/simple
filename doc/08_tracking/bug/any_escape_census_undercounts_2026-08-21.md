# `check-any-escape-census.shs` reports a number that describes 40% of its own scope

- **Filed**: 2026-08-21 by agent Y1 (`Any` inventory), cross-checking agent A5/Y2's gate.
- **Owner**: A5/Y2 (`src/compiler/35.semantics/any_escape/**`,
  `src/app/check/any_escape_census.spl`, `scripts/check/check-any-escape-census.shs`).
  **Y1 has not edited any of those files** — this record is the hand-off.
- **Plan**: `doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md`
  §8.5, §8.7, §15 Phase 0 census, §20.5 rows Y1/Y2.

## What was observed

`sh scripts/check/check-any-escape-census.shs` reports:

```
0 Any site(s), 12 unanalyzable   (over 8 modules)
```

Its default scope is `ROOT="src/compiler/00.common/assurance"`
(`scripts/check/check-any-escape-census.shs:57`). That directory holds
**20** `.spl` files. 8 were analyzed; **12 — 60% of the scope — could not be
lowered and contributed nothing to the total.**

## What is NOT the defect (stated so the real one is not lost)

The `0` itself is **honest for what it measured.** An independent source-level
scan (`src/app/any_audit/**`, this agent) over all 20 files in that directory
finds **zero `Any` type annotations**. The only three occurrences of the token
`Any` in the whole directory are prose in a comment block:

- `src/compiler/00.common/assurance/unsafe_capabilities.spl:48-50` — the
  `type_erasure` capability's own doc comment (``Permits `Any` to exist inside
  the region``).

So this is not a case of the checker missing typed `Any` sites that a text scan
can see. There is no file:line where Y1 finds a typed `Any` and Y2 reports none,
because in that scope there are none to find. **The "vacuity defect in the
checker" hypothesis in the Y1 brief is not supported and should not be recorded
as fact.**

## What the defect actually is

Two things, both about the verdict rather than the analysis:

1. **The unanalyzable count does not affect the verdict.** 12 files that failed
   to lower are reported alongside a `PASS`. A file that cannot be lowered is
   not a file with zero `Any`; it is a file with an *unknown* `Any` count. Every
   other guard in this repo treats "nothing was checked" as ERROR
   (`.claude/rules/vcs.md`, the `ERROR — nothing was checked` convention). Here a
   60%-unanalyzable scope still passes, and the ratio can rise to 100% without
   the verdict changing. The same shape as the fail-open path filter that
   `check-seed-builds-push.shs` had to remove on 2026-08-18.

2. **The scope is a directory with no `Any` in it.** §8.7's named migration
   targets — monomorphization tables, generic result dictionaries, backend port
   callable fields — are in `src/compiler/40.mono`, `src/compiler/00.common`,
   `src/compiler/15.blocks` and `src/compiler/70.backend`, none of which the
   default scope reaches. The gate's own header says the default was narrowed
   for cost. That is a defensible trade, but it means the headline number is not
   a census of the population §8.7 cares about, and reading it as one is how
   "0 Any sites" gets mistaken for "the migration is done".

## Concrete `Any` sites the default scope never sees

All found by Y1's source scan, all real type positions, none in the census scope:

| file:line | class | text |
|---|---|---|
| `src/compiler/40.mono/monomorphize/engine.spl:48` | generic | `specialized_functions: {text: Any}` |
| `src/compiler/40.mono/monomorphize/engine.spl:79` | generic | `generic_functions: {text: Any}` |
| `src/compiler/40.mono/monomorphize/cache.spl:103` | field | `value: Any` |
| `src/compiler/40.mono/monomorphize/cache.spl:126` | ret | `me lookup(key: text) -> Any?:` |
| `src/compiler/40.mono/instantiation.spl:34` | generic | `cache: Dict<text, Any>` |
| `src/compiler/00.common/compilation_context.spl:97` | field | `ast_data: Any` |
| `src/compiler/00.common/compilation_context.spl:113` | generic | `types: Dict<text, Any>` |
| `src/compiler/00.common/compilation_context.spl:184` | ret | `fn di_container() -> Any` |
| `src/compiler/15.blocks/blocks/registry.spl:29` | generic | `blocks: Dict<text, Any>` |
| `src/compiler/15.blocks/blocks/registry.spl:212` | param/ret | `fn with_block(block_def: Any, body: fn() -> Any) -> Any:` |
| `src/compiler/70.backend/arch_rules.spl:95` | param | `fn parse_arch_rules_from_sdn(sdn: Any) -> text:` |

## Requested fix (A5/Y2 owns the change)

1. Make the unanalyzable count **load-bearing**: either fail, or state it in the
   verdict line in a form that cannot be read as coverage — e.g.
   `PASS — 8 of 20 module(s) analyzed (12 unanalyzable), 0 Any site(s)`, and
   ERROR when the analyzable fraction falls below a recorded floor. A PASS whose
   denominator is invisible is the problem.
2. Record *why* each of the 12 fails to lower. If it is one shared cause, that
   cause is the actual blocker on widening the scope.
3. Widen the default scope, or say plainly in the verdict that it is not the
   §8.7 population.

## Cross-check available

Y1's independent source-level inventory is
`scripts/check/check-any-inventory-ratchet.shs` (scanner:
`src/app/any_audit/**`, metrics: `doc/10_metrics/any_inventory/`). It is a
weaker analysis (text, not HIR — it cannot see through aliases) but it has a
number for every file that exists. The two gates disagreeing on any file is the
signal worth chasing; they agree on the assurance directory today.

## Update 2026-08-21 (A5/Y2 lane) — the driver was fail-open; fixed

Two distinct causes sat behind the 12 unanalyzable files, and only one of them
was the lowering abort.

**1. The parse-failure path did not exist.** `src/app/check/any_escape_census.spl`
called `parse_full_frontend` and used the result unconditionally. The Simple
parser RECOVERS from syntax errors and still returns a `ParserModule`, so a
malformed file was censused as a clean, zero-finding module — the denominator
shrank and the Any/escape totals fell, which reads as progress. The gate's own
selftest caught this and was RED:

```
selftest: unanalyzable fixture was accepted (rc=0) — the census denominator is fail-open
FAIL — selftest failed; no scan was attempted
```

Fixed: `census_one` now checks `parser_has_errors()` /
`parser_get_errors()` (`src/compiler/10.frontend/core/parser.spl:1119,1125`)
immediately after the parse, prints `PARSE-FAIL <path>` plus every parse error,
counts the file toward a new `CENSUS_UNANALYZABLE`, and returns non-zero;
`main` propagates that into the process exit code so
`check-any-escape-census.shs`'s per-file `_rc` test sees it. The `SUMMARY` line
gained an `unanalyzable=<n>` field. Verified against the selftest fixture:

```
PARSE-FAIL test/fixtures/any_escape/unanalyzable.spl
  parse-error line 10:12: expected parameter name
  ...
SUMMARY modules=0 any_sites=0 escapes=0 unanalyzable=1
rc=1
```

**2. The standalone-lowering abort** that made real compiler files unanalyzable
is separately RESOLVED — see
`doc/08_tracking/bug/standalone_hir_lowering_aborts_on_real_compiler_files_2026-08-21.md`.
It was never in `20.hir`: it aborted inside `flat_ast_to_module` during PARSE,
and it is green as of `b5821b5daa2` / `e8e20d3c053`.

## Update 2026-08-21 — full scope now analyzable; the newly-visible findings look like FALSE POSITIVES

With the standalone-lowering abort resolved and the parse-failure path wired in,
`sh scripts/check/check-any-escape-census.shs` now analyzes **20 of 20** files,
up from 8 of 20. The verdict is:

```
FAIL — 20 module(s) checked, 6 Any site(s) (baseline 0), 2 escape(s) (baseline 0): the population GREW
```

That is not growth: those 8 findings were always there, in the 12 files the
census could not read. The denominator problem this record was filed about is
fixed; the numerator is now honest for the first time.

**The baseline was deliberately NOT regenerated.** All 8 findings sit in a
single file, in two sibling functions:

```
E-MC-ANY-001 outside_unsafe  formal_delivery_gates.spl evaluate_formal_delivery_gates_v1  19, 107, 145
E-MC-ANY-002 escape_operator formal_delivery_gates.spl evaluate_formal_delivery_gates_v1  154
E-MC-ANY-001 outside_unsafe  formal_delivery_gates.spl evaluate_formal_delivery_gates_v2  19, 165, 203
E-MC-ANY-002 escape_operator formal_delivery_gates.spl evaluate_formal_delivery_gates_v2  212
```

Reading those lines, none of them is a type erasure:

- **line 19** is `fn name() -> text:` / `match self:` inside the gate enum — a
  total match over a bare enum, no `Any` anywhere near it.
- **line 145** is `val release = match verified_release_bundle:` — a match
  EXPRESSION whose result type the checker apparently could not resolve.
- **lines 154 / 212** are inside the multi-line `if … or` continuations at
  147-152 and 205-210 — the exact construct
  `doc/08_tracking/bug/twelve_verification_assurance_specs_broken_not_flaky_2026-08-21.md`
  item 1 records as a **parser defect** in this same file
  (`parse: Unexpected token: expected expression, found Dedent`).

So the likely cause is unresolved match-expression / continuation-condition
result types surfacing as `Any` in HIR, not real erased values. Baselining
`any_sites=6, escapes=2` would freeze that artifact into the ratchet and make
the eventual real number unreachable without an unexplained "improvement".

**Hand-off (A5/Y2 + whoever owns `10.frontend` parsing):** either fix the
match-expression result typing so these resolve, or confirm they are genuine and
regenerate the baseline as a reviewed update. Until then the gate is honestly
RED, which is the correct state — it is red because it can finally see.

**Separate gap, not fixed here** (`scripts/check/**` is another lane's):
`run_census` has no per-file timeout, so one pathological file would hang the
whole gate indefinitely with no verdict. Every other guard in this repo treats a
non-terminating check as fail-closed; this one cannot, because it never returns.
