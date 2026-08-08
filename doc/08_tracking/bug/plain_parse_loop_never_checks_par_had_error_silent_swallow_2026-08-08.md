# The plain (non-entry-closure) parse loop never checks `par_had_error_get()` — parse errors are silently swallowed

- **ID:** plain_parse_loop_never_checks_par_had_error_silent_swallow_2026-08-08
- **Date:** 2026-08-08
- **Status:** OPEN — confirmed by call-site enumeration; not fixed
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
