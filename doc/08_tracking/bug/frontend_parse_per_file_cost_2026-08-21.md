# Front-end parse costs seconds per file; string-interpolation expansion is superlinear

- **Date:** 2026-08-21
- **Area:** `src/compiler/10.frontend/**` (self-hosted front end)
- **Symptom:** stage1 bootstrap `[build] parse N/662` advances at ~11 files/min
  (~5 s per mostly-small `.spl` file). Parse of 662 files should be seconds.

## Measurement

Probe: `parse_and_build_module_scoped()` driven directly, phases split by the
level-gated `SIMPLE_PARSE_PHASE_PROFILE=1` counter added to
`src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl`
(`PARSEPHASE` lines). Run under `bin/simple` (seed, e73a0bec647). Note the
probe module itself falls back off the JIT, so the ABSOLUTE numbers are
inflated versus stage1; the RATIOS between two files in the same run are the
evidence.

Whole-file cost, three sizes (pre-fix):

| file | bytes | parse+bridge | ms/KB |
|---|---|---|---|
| `10.frontend/core/lexer_types.spl` | 1,830 | 418 ms | 228 |
| `80.driver/driver_types.spl` | 63,143 | 18,814 ms | 298 |
| `50.mir/_MirLoweringExpr/switch_operators_calls.spl` | 273,667 | 196,800 ms | 719 |

Cost per KB rises 228 -> 298 -> 719: the front end is **superlinear in file
size**, not merely slow. Re-parsing a small file after a large one costs the
same as before it (474 ms / 486 ms / 550 ms across an interleaved A-B-C-D
sequence), so there is **no cross-file leak** — the superlinear term is
intra-file.

Phase split (µs), pre-fix:

| phase | lexer_types (1.8 KB) | driver_types (63 KB) | growth for 34x size |
|---|---|---|---|
| `parse_module_body` | 392,307 | 13,413,936 | **34x (linear)** |
| `expand_string_interpolations` | 2,969 | 3,801,002 | **1280x** |
| `expand_interpolated_placeholder_call_args` | 7,560 | 1,330,109 | **176x** |
| `desugar_collections` | 2,159 | 89,200 | 41x |
| `compiler_coverage_inventory_record_module` | 14 | 22 | — |
| `flat_ast_to_module` (bridge) | 26,304 | 644,766 | 24x |

`parse_module_body` dominates absolutely but scales **linearly** — its constant
is interpreter-execution cost, not an algorithmic defect (and is inflated here
by the probe's JIT fallback). The two interpolation phases are the algorithmic
defect: together they went from 0.25% of the small file to 27% of the medium
file, and they are what makes cost per KB rise with size.

## Defects and mechanism

### D1 — placeholder-free literals paid a full sub-parse (superlinear)

`src/compiler/10.frontend/core/string_interpolation_expand.spl`,
`expand_interpolated_placeholder_call_args`.

For **every** call-argument string literal it called
`parse_string_interpolation_parts(value)`, which calls
`parse_interpolation_fragment(inner)` per `{...}` region — a full
`lex_init_with_path` + `parser_advance` + `parse_expr` **sub-parse** that mints
fresh AST nodes into the shared arena. Only *after* that did it test
`expr_has_placeholder(parts[p])` and, in the overwhelming majority of cases,
discard the whole thing.

The superlinearity is the feedback loop: the minted nodes extend `expr_count()`,
and `expr_count()` is the bound of the enclosing `while idx < expr_count()`
walk — so the walk re-visits its own output, and any minted call node with a
string argument is sub-parsed again.

A placeholder is spelled `_`, `_0`, `_1`, …; a literal with no `_` character
anywhere cannot yield one. Fix: guard on `expr_get_str(a).contains("_")` before
the scan. Exact, not approximate.

### D2 — `decode_interpolation_brace_escapes` rebuilt every plain literal

Same file. It rewrites only `{{` -> `{` and `}}` -> `}`, but did so by walking
the literal one character at a time — `value[i:i+1]` allocates a substring per
character and `result = result + ch` reallocates the accumulator per character,
so it is quadratic in the literal's length — and it ran over **every**
non-interpolated string literal in the module, all of which decode to
themselves. Fix: return `value` unchanged when it contains neither doubled
brace.

### D3 — `parse_string_interpolation_parts` scanned brace-free literals

Same file. Every branch of its scanner is gated on seeing `{` or `}`, so a
literal with neither always returns `[]` — after paying the same per-character
`value[i:i+1]` substring allocation. Fix: early `return []`.

## Suspects checked and CLEARED

- **(a) O(n) UTF-8 string indexing in the lexer** — already fixed: the lexer
  scans a pre-split `source_chars: [text]` array (`lexer_struct.spl:146`), not
  `source[i]`.
- **(b) token arrays cloned per peek/advance** — no token array exists. The
  parser is streaming single-token (`lex_next_snapshot()`); there is nothing to
  clone.
- **(c) parser re-lexing from file start** — backtracking is
  `lex_snapshot_save`/`restore` (`lexer.spl:761`), O(indent depth), bounded and
  local. No `line_of(pos)` newline recount exists.
- **(d) FlatAstBridge linear `find` per node** — the bridge is index-addressed;
  its loops are over each node's own child lists. It measured 24x for 34x size
  (sublinear), so it is not the superlinear term.
- **(e) per-call env rebuild for tiny hot functions** — already fixed on the
  seed side by CowEnv: exported functions share one `Arc`-based
  `Env::with_base` (`evaluation_helpers.rs:824`) and `CowEnv::clone` is
  `Arc::clone` for base and scope (`value.rs:1059`).
- **(f) `[gc-warning]` / diagnostic formatting on a hot path** — the parser's
  diagnostic mirror writes only on the (cold) error path
  (`parser.spl:211` comment, verified), and phase timing shows no diagnostic
  cost.
- **env-var mirroring of the AST arena** (`expr_env_mirror_enabled`) — gated on
  `SIMPLE_BOOTSTRAP=1`, which is **not** set in the running stage1's
  environment. Off, and not a contributor here.

## Pre / post

Controlled A/B: ONE tree, ONE binary (`bin/simple`, seed e73a0bec647), the fix
reverted with `git checkout --` and restored, nothing else changed.
`test/05_perf/frontend_interpolation_scaling_spec.spl` parses a synthetic
module of 20 and then 40 functions, each carrying three call-argument
interpolated string literals.

| | 20 decls | 40 decls | ratio for 2x size |
|---|---|---|---|
| pre-fix | 5.38 s | 17.35 s | **3.23** (superlinear) |
| post-fix | 6.57 s | 11.68 s | **1.78** (linear) |

The spec's 3.0 bound therefore discriminates: RED before the fix, GREEN after.
Read the RATIO, not the absolute seconds — this host was running at load
average 21-64 throughout, and the absolute numbers move by 2x between runs of
identical code. That load is also why no reliable absolute pre/post claim is
made for `driver_types.spl`: the normalised phase shares moved in both
directions across repeat runs, so the honest statement is that the fixes remove
provably-unnecessary work and remove the superlinear term, not that they
deliver a specific speedup on that file.

## Round 2 (same day): operation counters, and what the passes were really doing

Timing alone could not say whether the interpolation passes were doing
avoidable work or merely running on a slow host, so the profile gained
OPERATION counters (`PARSESTAT`, same `SIMPLE_PARSE_PHASE_PROFILE=1` gate):
string literals seen, real `lex_init_with_path` + `parse_expr` sub-parses,
placeholder-bearing call arguments, nodes walked, and microseconds spent inside
sub-parses. The `placeholder` bucket was also split into its two functions.

`src/compiler/80.driver/driver_types.spl` (63 KB), after round 1:

| counter | value |
|---|---|
| string literals seen | 225 |
| sub-parses | 211 |
| placeholder call args | **0** |
| nodes walked | 3,446 |
| µs inside sub-parses | 17,663,691 of the 19,279,708 µs `interp` phase (**92%**) |

Two conclusions, both of which contradict the obvious guesses:

- **`expand_string_interpolations` is NOT doing avoidable work.** 211
  sub-parses for 225 literals is one per `{...}` region, each exactly once; the
  walk itself is 3,446 nodes (~1.6 s, i.e. cross-module call overhead at the
  same ~0.5 ms/node the rest of the interpreter runs at) and 92% of the phase
  is inside genuine fragment parsing. It is proportional. There is no
  re-walking of the full expr table per literal and no per-char rebuild left.
- **The placeholder passes were doing work on a module with ZERO placeholders.**
  `ph_args = 0`, yet `transform_placeholder_call_args_after_interpolation` cost
  3.34 s: it allocated an `initial_expr_count`-long `[bool]` marks array one
  `.push` at a time, walked every arm pattern, then walked the whole expression
  arena rebuilding argument arrays — to change nothing.

### D4 — placeholder transform passes ran unconditionally

`src/compiler/10.frontend/desugar/placeholder_lambda.spl`,
`transform_placeholder_call_args_after_interpolation` and
`transform_interpolated_placeholder_args`.

A placeholder is always an `EXPR_IDENT` named `_` or `_N`
(`detect_placeholder_mode` is the authority; every other tag it handles only
recurses toward such an ident), and both passes can change an argument only
through `transform_placeholder_lambda`, which returns a different node only
when the subtree holds one. So "no placeholder ident anywhere in the module" is
an EXACT no-op precondition. Added `module_has_placeholder_ident(limit)`: one
pass of two direct module-global array reads per node, no allocation, no
cross-module call.

| `driver_types.spl` phase | before D4 | after D4 |
|---|---|---|
| `transform_placeholder_call_args_after_interpolation` | 3,341,323 µs | **42,875 µs** (78x) |
| `expand_interpolated_placeholder_call_args` | 869,058 µs | 330,292 µs |
| `expand_string_interpolations` | 19,279,708 µs | 8,215,660 µs (unchanged in share) |
| `parse_module_body` (load normaliser) | 103,377,959 µs | 48,491,817 µs |

Normalised against `parse_module_body` in the same run (this host's load swings
2x between runs of identical code, so shares are the honest unit), the
placeholder transform fell from **3.23% of parse time to 0.088%** — a 37x
reduction in share. `expand_string_interpolations` held its share, exactly as
the counters predicted: its cost is real work.

## Still open

`parse_module_body` remains the dominant term (70-91% of parse time in every
measurement above) and scales LINEARLY with a large constant. That is
interpreter-execution cost in the self-hosted parser, not an algorithmic
defect, and it is the term that has to come down for stage1 to reach the
"couple of minutes" target. It is a separate piece of work from this record,
and it needs measuring on a JIT-resident path: the probe used here falls back
off the JIT (`unresolved external symbol 'parse_and_build_module_scoped'`), so
its absolute constant is inflated relative to stage1's.

The `expand_string_interpolations` phase also remains costly on
interpolation-dense files: its sub-parses there are genuine work (a real
`{expr}` region must be parsed), and the three fast paths added here only skip
literals that provably need nothing. Making the genuine case cheaper would mean
not re-entering the lexer per fragment at all, which is a design change, not a
guard.

## Reproduce / regression pin

`test/05_perf/frontend_interpolation_scaling_spec.spl`, two examples:

1. **Scaling.** Doubles the number of call-argument interpolated string
   literals and asserts parse cost does not more than triple (3.23 pre-fix ->
   1.78/1.79 post). Pins the superlinearity, not a machine-specific number.
2. **Sub-parse count.** Asserts that a 10-function module with 30 literals and
   60 `{...}` regions performs **exactly 60** sub-parses — one per region and
   not one more — read from the `si_stat_subparse_count()` counter. This is the
   pin a wall-clock bound cannot be: it distinguishes avoidable work from a
   slow host, and it is the counter that proved
   `expand_string_interpolations` innocent and the placeholder passes guilty.
