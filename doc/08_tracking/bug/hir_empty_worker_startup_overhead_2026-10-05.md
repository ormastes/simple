# HIR worker startup exceeds available module work

Status: OPEN performance investigation; no fix or speedup verified.

The new Phase 2 producer
`3bd458857152a0c1be96b08f21c87ebd686c3f155a87f0f0eb7633d1bd2b07cb`
compiled and ran `test/04_smoke/windows_native_hello.spl` successfully in
`runtime/windows-restart-20261004/qualification-60cd7f-warm916-hello20`.
The compile log contains 20 distinct `[hir-shard] done shard=N/20` records.
Only shard 10 lowered one module; 19 workers lowered zero modules.
This proves the explicit HIR path was exercised, not twenty useful workers
or a throughput improvement.

The qualification reports 123.162 seconds compile wall time and 12,042,164
KiB process-tree peak RSS. Empty worker startup is a plausible contributor;
these measurements do not isolate its cost from source admission, frontend
setup, cache validation, linking, or collector overhead.

Investigate capping the number of launched HIR workers by available independent
work, while preserving configured capacity (including 20, 80 and 128), owner
receipt correctness, dependency barriers, deterministic merge and crash recovery.
Do not silently change the requested job allocation or impose a fixed worker
limit. Keep active requests and caches unchanged during diagnosis.

Required regression cases: zero modules, one module, fewer modules than the
worker budget, more modules than the budget, skewed dependency levels, cache
hits, worker crash and retry. Require identical native output, unique claims,
complete receipts, no lost work and no additional memory or logic regression.
Benchmark warm and cold elapsed time plus process-tree RSS against the same
producer/source/options baseline. These cases remain UNRUN.

## 2026-11-07 focused-route source mitigation — qualification NOT_RUN

The ordinary coordinator already applies
`native_build_shard_count_for_closure_v1` after memory admission. The opted-out
focused capsule HIR branch did not. This narrow change applies the same existing
production helper there, using the already published closure selected count and
SIMPLE_SHARD_SMALL_CLOSURE_MAX. It adds no source walk, new environment authority,
fixed worker ceiling, lifecycle change or change to parse/per-file worker routes.
The existing focused `hir_count > 1` launch gate remains intact.

This is a partial mitigation, not closure of this report. The historical Windows
log summary above does not retain enough invocation/closure-publication detail
to prove that it used this current focused branch or had a known closure count.
No claim is made that the historical123s case now improves. Plain/positional
per-file bootstrap branches prepublish closure before the focused prepass;
Stage3/4 focused branches do not universally do so. When no closure is published,
count remains -1 and the canonical helper preserves the admitted worker count.
It must not be treated as zero work or reconstructed from untrusted argv.

Follow-up plan for unknown-count routes: establish one coordinator-owned closure
publication after source authority, using the existing
native_build_coordinator_prepublish_closure_v1/native_build_closure_publish_once_v1
owner. Reuse that exact selected generation in workers and the later in-process
build, rather than adding another closure walk. First verify source/policy/library
mode bindings and whether a compatible publication already exists; no such
publication-routing change is included here.

Focused controls and finite native plan:
`test/01_unit/app/cli/focused_hir_closure_admission_spec.spl` and its doc/06_spec
manual. All runtime controls remain NOT_RUN. Static source review is distinct
from actual child launch counts, successful outputs and measured RSS/latency.
