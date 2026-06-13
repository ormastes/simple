# Lean-parser parse_module is superlinear and degrades per call (interp AND compiled stage4)

- **ID:** interp_parse_superlinear
- **Severity:** P2→P1 (perf; CONFIRMED in compiled stage4 production frontend
  2026-06-13 — makes the full src/lib parser-completion sweep gate infeasible
  until fixed; does not block correctness or per-gap-class iteration)
- **Date:** 2026-06-12 (compiled confirmation 2026-06-13)
- **Component:** lean frontend (`src/compiler/10.frontend/core/`), both seed-interpreted AND compiled stage4
- **Status:** OPEN

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

## CONFIRMED in compiled stage4 (2026-06-13) — production frontend, not just interp

Host stage4 (compiled lean parser, `SIMPLE_FRONTEND_DELEGATED=1`)
`check src/app/debug/remote/breakpoint_manager.spl` timed out at 180s having
flushed 0 parser errors — still parsing the import closure. The docker check
(600s) flushed only a partial 101. Compiling does not change the algorithm.
This makes the **full src/lib sweep gate infeasible** until fixed — a
prerequisite for that gate (tracked in parser_completion.md M12) — but it does
NOT block per-gap-class iteration, which runs on tiny synthetic probes (fast in
both seed-interpreted and host-stage4-compiled modes).

### Fix sketch (do NOT implement mid-gap-loop — it would corrupt the diagnostic instrument)
`par_text_get`/`parser_token_text_from_offsets` is the token-text source every
gap-class diagnosis reads; a subtly-wrong fix in compiled mode reintroduces the
RW-shadow class and silently corrupts parses → phantom "gap classes". Keep it
frozen while measuring with it. When ready, as its own task: cache the source
ONCE per parse in a module-level slot (written when `SIMPLE_BOOTSTRAP_LEX_SOURCE`
is set), read there instead of `rt_env_get` per token. Make the slot
WRITE-ONCE / READ-MANY (never read+write in the same fn — that is the RW-shadow
failure). Validation REQUIRES slow full-closure runs + a correctness re-sweep.

## Suspects (not yet profiled)

- `parser_token_text_from_offsets` re-fetches the ENTIRE source from
  `rt_env_get("SIMPLE_BOOTSTRAP_LEX_SOURCE")` and slices it for EVERY token
  (`core/parser.spl:100-113`); `parser_advance` calls it per token.
- Allocate-and-leak runtime: per-call heap growth degrades all subsequent
  string ops (see also `rt_string_concat_quadratic_2026-06-12.md`, same-day
  finding in the MCP hot path).

## Impact / workaround

- Interpreted host pre-sweeps over src/lib are untenable (~100+ hours);
  parser-gap discovery moved to the compiled stage4 docker check (fast).
- Probes/harnesses: keep sources tiny (<40 lines) and prefer one parse per
  process when timing matters.

## Repro

- `tmp/site12/timing_probe.spl`, `tmp/site12/perf_ab_probe.spl` (marker-file
  mtimes give per-step timings; print buffers are lost on timeout-kill).
