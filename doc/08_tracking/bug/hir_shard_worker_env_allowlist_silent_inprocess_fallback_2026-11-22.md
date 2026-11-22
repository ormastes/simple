# HIR shard worker env allowlist silently degrades to in-process HIR

- **Date:** 2026-11-22
- **Status:** open
- **Severity:** P2

## Symptom

Unknown `SIMPLE_*` keys in the build environment (for example `SIMPLE_PHASE_RSS`) make the HIR worker pool refuse to start. HIR then runs in-process with no hard error, so a whole build silently loses HIR parallelism.

## Evidence

The allowlist lives in `src/app/cli/worker_hir_profile_v1.spl`. Observed during Phase 3 full-CLI builds: setting an extra `SIMPLE_*` key changed the build from sharded HIR workers to a single in-process HIR pass with no diagnostic naming the key.

## Repro

Run a Phase 3 native-build with `SIMPLE_PHASE_RSS=1` exported alongside the normal build env; HIR runs in-process.

## Workaround

Unset every `SIMPLE_*` key not in the allowlist before launching the build.

## Fix direction

Fail closed with an error naming the offending key, or ignore keys that do not affect worker semantics.
