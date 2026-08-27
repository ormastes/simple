# Compiler, loader, and cross-language performance operator guide

Status: evidence-guided draft. This guide describes how to operate the
performance profile and how to decide whether a row may be quoted. It does not
claim a final Stage 4 result, and no build or benchmark was run while drafting
it.

## Start with the admission rule

Use the repository profile entrypoint and its report contract:

```sh
SIMPLE_BINARY=build/perf-final/full/x86_64-unknown-linux-gnu/simple \
SIMPLE_COMPILER_PROVENANCE=build/perf-final/full/x86_64-unknown-linux-gnu/simple.provenance.env \
SIMPLE_NO_STUB_FALLBACK=1 RUNS=20 \
sh scripts/check/check-cross-language-perf.shs
sh test/05_perf/profile_scripts/profile_report_contract_test.shs
```

The harness requires a self-hosted compiler, canonical Stage 3 or adjacent
Stage 4 provenance, no stub fallback, checksum-verified workloads, raw samples,
p50/p95, and max RSS. Do not allow the harness to auto-select a Rust seed or
debug compiler: both the admitted executable and its adjacent provenance
receipt are mandatory inputs.

Rows from a Rust bootstrap seed, a stale release wrapper, an unverified source
execution mode, a failed compile, a missing checksum, or a report with the
contract skipped are diagnostic only. In particular, the June profile tables
are useful for direction but are not release-admissible under the current
identity and actual-mode rules; see
`/mnt/data/bs2/simple-perf-final-9c/doc/09_report/cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md`.

## Pick the execution mode deliberately

| Mode | Operator use | Evidence requirement |
|---|---|---|
| Source/interpreter | edit-run iteration and semantic oracle | exact actual-mode receipt; no JIT fallback silently labeled interpreter |
| SMF loader | cached bytecode comparison and warm deployment | exact SMF-loader receipt, artifact identity, checksum, and fresh source/dependency validation |
| Native | production throughput and memory probes | admitted compiler provenance, fresh artifact identity, checksum, and bounded RSS |

The mode definitions and normal commands are documented in
`doc/07_guide/compiler/check_perf.md`. Do not combine source, SMF, and native
numbers into one Simple average.

## Loader/cache checklist

For user scripts, the retained research describes `try_load_smf_cached` using a
manifest, source SHA-256, and dependency interface hashes; a fresh artifact is
loaded and a stale artifact falls back to compilation. See
`/mnt/data/bs2/packed-memory-32ead/.spipe/perf-opt-lang-web-db-os/research/02_smf_idle_cache.md`.

The separate dynSMF precompiled-library lane historically checked only SMF
magic and recorded background compile commands without dispatching them. Treat
that lane as partial until its source-hash invalidation, actual dispatch, and
integration evidence are present. The same research file is the source of this
qualification.

The loader architecture investigation records the intended split: Simple owns
orchestration and policy, while low-level parsing/memory operations are kept in
the runtime; mmap-backed SMF caching is an implementation technique, not proof
of a measured startup win. Source: `doc/09_report/2026/02/loader_architecture_investigation_2026-02-04.md`.

## Actual-mode and seed caveats

The measured process must report the engine that actually executed it. A command
request alone is insufficient because dispatch can cross a process boundary or
fall back. The retained blocker and receipt contract are at
`/mnt/data/bs2/simple-perf-final-9c/doc/08_tracking/bug/cross_language_actual_execution_mode_receipt_missing_2026-08-12.md`.

Do not promote a Stage 3 diagnostic or quote final Stage 4 performance until a
fresh provenance receipt is adjacent to the exact executable and the positive
interpreter/SMF/native mode gates pass. That same retained blocker explicitly
keeps fresh Stage 3/4 execution required.

## Memory-bug handling

When a memory claim is made, retain the fixture, requested size, output length,
content/checksum proof, elapsed sample, and total process RSS. The accepted
pre-migration baselines were 200,292 KiB maximum RSS for the parser fixture and
449,272 KiB for 10,000 distinct short strings; those are context baselines, not
current release passes. Source:
`/mnt/data/bs2/packed-memory-32ead/doc/09_report/perf/interpreter_shared_text_rss_baseline_2026-07-13.md`.

The same retained report sets post-migration ceilings of 220,321 KiB and
494,199 KiB. Its later bounded parser evidence records 33 ms and 75 ms for the
small parser fixtures with 205,192 KiB maximum RSS, while the larger bootstrap
acceptance remains pending. Source:
`/mnt/data/bs2/packed-memory-32ead/doc/09_report/perf/interpreter_shared_text_compile_wip_2026-07-13.md`.

Never infer memory safety from allocation intent, requested byte count, or a
zero checksum alone; require the retained output-length and RSS row.

## Missing techniques to track

The current performance program proposes, but does not by itself prove,
semantic incremental identity/CAS, demand-driven compiler queries, register
bytecode, adaptive quickening, a low-latency native tier, precomputed aspect
plans, and a persistent compiler service. These are design targets rather than
measured wins. Source: `doc/03_plan/compiler/perf/compiler_interpreter_performance_program_2026-08-10.md`.

For an optimization change, measure in this order: algorithm/data layout,
allocation and copy removal, dispatch reduction, then local cleanup. Keep the
semantic oracle and all three execution modes covered; record a concrete bug
when a compiler/runtime blocker prevents parity. The repository optimization
workflow is `/.codex/skills/optimize/SKILL.md`.

## Operator handoff

Attach the report path, source revision, compiler path and SHA-256, provenance
receipt, requested/actual mode, fallback flag, checksum, raw wall samples,
p50/p95, max RSS, and rejection reason for every unavailable row. A row without
that chain is an investigation result, not a performance claim.
