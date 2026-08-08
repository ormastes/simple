# The plain (non-entry-closure) parse loop never checks `par_had_error_get()` — parse errors are silently swallowed

- **ID:** plain_parse_loop_never_checks_par_had_error_silent_swallow_2026-08-08
- **Date:** 2026-08-08
- **Status:** FIXED 2026-08-08 — see "Fix and control pair" at the bottom.
  Originally filed OPEN after call-site enumeration.
- **Severity:** high — a *silent-swallow* fail-open. Unlike a stop-at-first-error
  bug, which under-reports loudly, this one loses the diagnostic entirely.

## The finding

`par_had_error_get()` is called at exactly **three** places in
`src/compiler/80.driver/driver_source_pipeline_parsing.spl`, enumerated with
`/usr/bin/grep` (not the ugrep wrapper, which honours `.gitignore`):

| line | context | checks errors? |
|------|---------|----------------|
| 9 | the `use` import itself | n/a |
| 83 | `add_streaming_module_surface` | yes — returns `Err` on first error |
| 210 | `parse_all_impl`, entry-closure branch | yes — collects all (fixed `1266a61d9a6`) |

But `parse_full_frontend` is invoked at **five** sites: 81, 203, 303, 370, 417.
The plain non-entry-closure parse loop — `parse_full_frontend` at **line 370**,
inside the loop that begins around line 350 (`var parsed_modules: Dict<text,
ParserModule> = self.ctx.modules`) — and the single-module path at **line 417**
never consult `par_had_error_get()` at all.

Consequence: on those paths a parse error sets the parser's internal flag, the
loop ignores it, nothing is ever pushed to `ctx.errors`, and compilation proceeds
with a module whose AST is missing or truncated. The failure surfaces later as an
unrelated-looking downstream error (an undefined symbol, an empty module) or not
at all.

## Why this is a different defect from the one just fixed

`1266a61d9a6` made the entry-closure parse loop collect all parse errors instead
of returning on the first. That is an *under-reporting* bug: the first error was
always reported correctly. This one is a *no-reporting* bug — the error never
enters `ctx.errors` on any iteration, so no amount of collect-all behaviour
recovers it. Fixing one does not fix the other, and the fix landed for the
entry-closure path does not touch these sites.

This belongs to the same family as the rest of the 2026-08-07/08 audit findings:
a verification or diagnostic path that structurally cannot observe the condition
it appears to cover. See
`doc/09_report/infra/aot_lane_regression_fence_audit_2026-08-07.md` and
[[reference_repo_verification_layer_is_fail_open]].

## Suggested fix

Mirror the shape now used at line 210 (post-`1266a61d9a6`): after each
`parse_full_frontend` call at 370 and 417, check `par_had_error_get()`, push a
`parse error in {source.path}` diagnostic to `self.ctx.errors`, and — for the
loop at 370 — `mark_module_poisoned` + `poison_budget_exhausted()` + `continue`
so the collect-all default applies uniformly across parse paths.

Note `par_had_error` is reset per-file inside `parser_init_with_path`
(`parser.spl:254`), so a per-iteration check cannot leak a stale flag into the
next source. That property is what makes the loop-and-continue shape safe, and it
holds for these sites too.

## Verification for whoever picks this up

The entry-closure path is already covered — two deliberately-broken files under
`--entry-closure` report both parse errors and zero spurious "internal
entry-closure parse cache miss" lines (verified 2026-08-08 against the landed
tree).

For THIS defect the repro must avoid `--entry-closure`, so it routes through the
line-350 loop instead. Correct post-fix behaviour: a syntax error in a
non-entry-closure module produces a `parse error in <path>` diagnostic and a
nonzero exit, rather than a downstream undefined-symbol error or a silent
success.

Do not verify by asserting the CURRENT output — confirm the diagnostic is
genuinely absent today first, or the test will pin the bug as expected behaviour.

## Fix and control pair (2026-08-08)

Fixed at **four** sites in `driver_source_pipeline_parsing.spl` — the doc's
enumeration missed one: the `SIMPLE_BOOTSTRAP=1` entry-source loop (line 303)
had the same silent swallow, and that is the loop Stage 2/3 actually runs. All
four now check `par_had_error_get()` and push `parse error in {path}`:

| site | path | shape |
|------|------|-------|
| ~303 | `SIMPLE_BOOTSTRAP=1` entry loop | push + poison + budget, module not stored |
| ~370 | plain parse loop | push + poison + budget + `continue` |
| ~453 | `parse_source` single-module helper | push + poison (no loop to continue) |
| ~210 | entry-closure loop | already fixed by `1266a61d9a6` |

Verified with `build/collect-all-probe/parse_probe.spl` (gitignored scratch
harness, sibling of the `probe.spl` used by `52b19d55d86`), driving the
pure-Simple driver over two modules with independent SYNTAX errors — syntax, not
unresolved types, so the diagnostic can only originate from a
`par_had_error_get()` check in this loop:

```
BEFORE (negative baseline, confirmed on the pre-fix tree)
  [parser_error] ... mod_a.spl ... expected ), got EOF
  [parser_error] ... mod_b.spl ... expected ], got EOF
  errors=0  parse_errors=0        <- both diagnostics SWALLOWED

AFTER (default)
  errors=2  parse_errors=2        <- BOTH reported in one run

AFTER (SIMPLE_COMPILE_FAIL_FAST=1)
  errors=1  parse_errors=1        <- stop-at-first opt-out still works
```

Regression check: `probe.spl` (phase-3 lowering) unchanged — `multi` FAILURE,
`one` FAILURE, `clean` SUCCESS with 0 errors.

**Correction (same day, two lanes collided):** a parallel lane IMPLEMENTED
`--fail-fast` (commit `c54fe653535`, `src/app/io/_CliCompile/compile_targets.spl`
— the flag sets `SIMPLE_COMPILE_FAIL_FAST=1`, so both spellings work). This lane
had meanwhile rewritten the `driver_types.spl` comment to assert that no such
flag exists. That assertion was true when written and false an hour later; it has
been corrected to describe both entry points. The "Related" bullet below is left
in place as the historical record of why the flag was added.

## Related, found in the same pass

- `add_streaming_module_surface` (line 83) still returns `Err` on the first parse
  error rather than collecting. Streaming-only, gated behind four env vars
  (`SIMPLE_BOOTSTRAP` + `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE` +
  `SIMPLE_BOOTSTRAP_STAGE4` + `SIMPLE_STAGE4_STREAMING_SURFACES`), so it is
  low-exposure — but it is a stop-at-first, and should be brought in line.
- **`--fail-fast` does not exist.** `driver_types.spl:227` and
  `driver_hir_pipeline_lowering.spl:177` and `:439` all name a `--fail-fast` CLI
  flag in comments. No such flag is implemented; the working opt-out is the env
  var `SIMPLE_COMPILE_FAIL_FAST=1`. Either implement the flag or correct the
  three comments — a documented-but-absent flag sends readers hunting for a
  parser bug that isn't there.
