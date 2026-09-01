# Lean-parser parse_module is superlinear and degrades per call (interp AND compiled stage4)

- **ID:** interp_parse_superlinear
- **Severity:** P2 (perf). The parse-side per-token whole-source fetch is FIXED
  (2026-06-13). The remaining superlinear `check` cost on compiled stage4 was
  RE-ATTRIBUTED 2026-06-13 to a non-parse pass (type inference) — see "Compiled
  stage4 re-profile" below; that is a SEPARATE blocker for the full src/lib sweep
  gate, NOT a parser bug.
- **Date:** 2026-06-12 (compiled re-profile + parse fix 2026-06-13)
- **Component:** lean frontend (`src/compiler/10.frontend/core/`). Parse-side
  fetch: FIXED. Interpreter parse_module aging: still open (interp-only).
- **Status:** parse-side fetch FIXED; interp aging OPEN; compiled-`check`
  superlinearity is type-inference (tracked separately, see below)

## Symptom

Seed-interpreted `parse_module()` cost grows far worse than linearly with
source size, and successive calls in one process get slower even for
identical input. Practical effect: parsing a 470-line file takes 25-45 min
interpreted; multi-file sweeps misread slow files as hangs.

## Measurements (2026-06-12, load ~15, tmp/site12/timing_probe.spl + perf_ab_probe.spl)

Prefixes of src/lib/blink/css_parser/selector.spl, one process, sequential:

| lines | wall time |
|-------|-----------|
| 20    | <1 s      |
| 40    | +2 s      |
| 80    | +6 s      |
| 160   | +256 s    |

Equal-size (~40-line) synthetic cases, one process, sequential — identical
source parsed twice (cases 1 and 2) shows pure per-call aging:

| case (order) | content        | wall time |
|--------------|----------------|-----------|
| 1            | plain deep fns | 69 s      |
| 2            | SAME source    | 124 s     |
| 3            | `and` keyword  | 154 s     |
| 4            | `&&`           | 197 s     |
| 5            | `&` bitwise    | 194 s     |
| 6            | `\|\|`         | 185 s     |

Conditions (`and` vs `&&` vs `&` vs `||`) do not differ beyond the aging
trend — G32 lexer fusion is NOT implicated. Earlier "hang" reports on
selector.spl (sweep stuck 24+ min on the file, bisects "hanging" at moving
line numbers) were timeouts against this curve, not loops: all synthetic
construct probes (banner comments, Option<T> returns, String params,
open-if-at-EOF) parse instantly.

## Compiled stage4 re-profile + ROOT CAUSE FOUND & FIXED (2026-06-13) — env-var AST mirror, not type inference

An earlier note claimed compiled-stage4 parse was "CONFIRMED superlinear" because
`check <file>` timed out. Re-profiling located the real cause. Synthetic standalone
files of N trivial functions (6 lines each), `SIMPLE_FRONTEND_DELEGATED=1`, host
stage4, `check` wall time, BEFORE vs AFTER the fix:

| funcs | lines | `lex` only | `check` BEFORE | `check` AFTER |
|-------|-------|-----------|----------------|---------------|
| 100   | 600   | 0.25 s    | 52 s           | 15.3 s        |
| 200   | 1200  | 0.58 s    | 146 s          | 20.4 s        |
| 400   | 2400  | 0.99 s    | >300 s timeout | 39.4 s        |

200→400 ratio: 2.8×+ (superlinear) BEFORE → 1.9× (linear) AFTER. (An interim guess
attributed the cost to "type inference" — superseded; the cause is below.)

**ROOT CAUSE — per-index env-var AST mirror.** Every `stmt_alloc` wrote 6
`SIMPLE_BOOTSTRAP_STMT_<idx>_<field>` env vars (`ast_stmt.spl`) and every
`expr_alloc` ~10 `SIMPLE_BOOTSTRAP_EXPR_<idx>_<field>` (`ast_expr_part1.spl`). The
keys are per-index unique, so `environ` grows to O(nodes); libc `setenv`/`getenv`
linear-scan `environ`, so the write side (parse) and the read side
(`flat_ast_to_module`) are each O(N²). `stmt_reset`/`expr_reset` clear the arrays
but NOT the env vars, which also explains the interpreter per-call aging (table
above): `environ` accumulates across `parse_module` calls in one process.

**FIX (committed 2026-06-13).** The parallel module-var arrays (`stmt_*`/`expr_*`)
are written unconditionally by `alloc` + constructors and are the real store in
compiled stage4; the `*_get_*` readers are env-first/array-fallback with every
array populated (verified: `expr_alloc` pushes all 10 arrays; the generic env-only
`expr_i64_get`/`expr_text_get` have zero consumers — only `expr_get_*` are used).
So the per-index env writes are now gated behind `SIMPLE_BOOTSTRAP=1` (interpreter
bootstrap, where module vars don't persist): compiled reads fall back to the
correct arrays. See `doc/08_tracking/bug/ast_env_var_quadratic_parse_2026-06-13.md`.

**Correctness verified:** compiled stage4 (lean frontend) compiles+runs a
construct-varied program with exact output (if/elif/else, while, for, val/var,
binop precedence, ternary, array lit, string interp, calls); g45/g46 parse
canaries green; `perr=0` on all perf files.

**Conclusion:** the full src/lib sweep gate (parser_completion.md M12-4) prerequisite
is MET — compiled parse/check is now linear. A latent SECONDARY O(N²) remains but is
DEAD today: `generalize_all`/`env_free_var_ids` in
`src/compiler/30.types/type_infer/generalization.spl` (linear-scan `[i64]` sets) —
`infer_module` is not wired into the driver; fix (Dict-back the sets) when type
inference is enabled. Also minor/ungated: `module_add_decl` per-decl env key + 128
slot cap (`ast_part2.spl`) — secondary, only bites files with >128 top-level decls.

### Parse-side per-token whole-source fetch — FIXED 2026-06-13 (real but minor)
`parser_token_text_from_offsets` re-fetched the ENTIRE `SIMPLE_BOOTSTRAP_LEX_SOURCE`
via `rt_env_get` and re-sliced it per token (one per `parser_advance`) — a genuine
O(N²), but minor in absolute terms (see arithmetic above). FIXED: a generation-keyed
whole-source cache (`parser_lex_source_cached`, module-var slot) keyed on
`SIMPLE_BOOTSTRAP_LEX_SOURCE_GEN`, bumped at every LEX_SOURCE set-site
(`lex_init_with_path` + `parse_module`/`parse_module_file` restores). Semantics
preserved (slice + kind==3 unwrap unchanged). Compiled stage4 persists the slot;
interpreter falls back to per-call refetch (slow but correct — hence interp
parse_module aging below remains open). Lexer scanning already holds source in the
`CoreLexer` struct, so only the parser side needed the cache.

## Suspects for the remaining INTERPRETER parse_module aging (compiled fetch now FIXED)

- ~~`parser_token_text_from_offsets` whole-source re-fetch per token~~ — FIXED
  (see above); in the interpreter the module-var cache slot does not persist, so
  this still contributes to interp-only aging.
- Allocate-and-leak runtime: per-call heap growth degrades all subsequent
  string ops (see also `rt_string_concat_quadratic_2026-06-12.md`, same-day
  finding in the MCP hot path). Likely the dominant cause of the interpreter
  per-call aging (identical source parsed twice gets slower — table above).

## Impact / workaround

- Interpreted host pre-sweeps over src/lib are untenable (~100+ hours);
  parser-gap discovery moved to the compiled stage4 docker check (fast).
- Probes/harnesses: keep sources tiny (<40 lines) and prefer one parse per
  process when timing matters.

## Repro

- `tmp/site12/timing_probe.spl`, `tmp/site12/perf_ab_probe.spl` (marker-file
  mtimes give per-step timings; print buffers are lost on timeout-kill).
