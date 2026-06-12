# Interpreted lean-parser parse_module is superlinear and degrades per call

- **ID:** interp_parse_superlinear
- **Severity:** P2 (perf; blocks interpreted-mode parser sweeps/tooling, not correctness)
- **Date:** 2026-06-12
- **Component:** seed-interpreted execution of the lean frontend (`src/compiler/10.frontend/core/`)
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
