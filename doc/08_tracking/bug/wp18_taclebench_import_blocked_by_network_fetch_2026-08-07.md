# WP-18 TACLeBench import blocked: network fetch (`curl`/`wget`) is hard-blocked in this environment

Status: blocked (environment restriction), not scope-avoidance.

## Context

`doc/03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md` WP-18
reads: "Target timing model + WCET adapter + response-time report; import
TACLeBench as an independent corpus." The first three pieces (target timing
model, an honestly-labeled observed-max-execution-time measurement harness,
and a report-only response-time report) do not require the external corpus
and were landed separately — see:

- `src/lib/nogc_async_mut_noalloc/async/timing_model.spl`
- `src/lib/nogc_async_mut_noalloc/async/wcet_adapter.spl`
- `src/lib/nogc_async_mut_noalloc/async/response_time_report.spl`
- specs: `test/01_unit/lib/nogc_async_mut_noalloc/async/{timing_model,wcet_adapter,response_time_report}_spec.spl`

The TACLeBench-import half is genuinely blocked and out of scope for this
session.

## What's blocked and why

TACLeBench (https://github.com/tacle-bench/tacle-bench) is an external
benchmark corpus commonly used as an independent WCET-analysis test suite. To
"import TACLeBench as an independent corpus" requires fetching it from its
upstream source (git clone or HTTP archive download). This environment's
context-mode tooling hard-blocks both `curl` and `wget` (any Bash command
containing either is intercepted and replaced with an error message) and
denies `WebFetch` entirely, redirecting instead to `ctx_fetch_and_index` /
`ctx_execute` sandboxed HTTP calls. Verified directly this session: attempting
network fetch returns `context-mode: curl/wget blocked`.

Even the sandboxed `ctx_execute`/`ctx_fetch_and_index` routes are for
indexing/searching small amounts of fetched text into a knowledge base, not
for retrieving and materializing a multi-file external source corpus
(TACLeBench is a directory tree of C benchmark programs) into the repository
as tracked files. No amount of code-level investigation resolves a
network-level block — this is a hard environment restriction, not a
tractability question.

## What would unblock this

Either:
1. Run the import from an environment where network fetch to GitHub is
   permitted (outside this hard-blocked context-mode sandbox), producing a
   vendored corpus tree plus attribution/license notes, or
2. The user/operator supplies the TACLeBench source tree directly (e.g. as an
   uploaded archive) for import without a live fetch.

Do not fabricate corpus data pretending to be TACLeBench in either case — an
absent import must stay visibly absent, not simulated.

## Related

- Prior recorded note in the plan doc (commit `9b934c5a67d`,
  "docs(assurance): record WP-16 landing, WP-18 environment blocker") treated
  the whole of WP-18 as blocked; this doc narrows that to the corpus-import
  half specifically, since the timing-model/adapter/report pieces do not
  depend on the corpus and have since landed.
