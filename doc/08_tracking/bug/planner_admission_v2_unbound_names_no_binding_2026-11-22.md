# `planner-admission-v2-unbound` named no binding (2026-11-22)

Status: FIXED (diagnostic only; verification stays fail-closed).

Ledger: W20 in `C:/dev/simple-release-boot-20261122/build/rboot/WORKAROUNDS.md`
(Windows MSVC lane, release `8dae652711e`).

## Symptom

A Stage 3 resume printed only `bootstrap-policy-error: planner-admission-v2-unbound`.
The cause was a launcher that cd'd into the OLD worktree while the receipt and
pinned snapshot lived under `simple-release-boot-p3-20261122`. Nothing in the
message pointed at the root.

## Root cause

`scripts/check/lib/bootstrap-planner-admission-bound.shs`:
`bootstrap_planner_v2_verify_structure` and `bootstrap_planner_v2_verify_bound`
end each of roughly 50 checks in a bare `return 1`, and
`bootstrap_planner_v2_verify` printed one fixed line. For a different verifier
root the first check to fire is `planner_source_path`, which must equal
`<root>/src/app/cli/bootstrap_reason_planner.spl`. `runtime_dir` (`<root>/*`)
and the output root (`<root>/build/*` or `SIMPLE_BOOTSTRAP_EXTERNAL_OUTPUT_ROOT`)
fail the same way.

## Fix

New helper `bootstrap_planner_v2_unbound <binding> <expected> <actual>` records
the mismatch and returns 1. It is wired into the structural, path-pinning, and
digest re-derivation checks (schema, line count, key order, status, typed pair,
platform, each `*_path`/`*_sha256`, `planner_source_path`, `runtime_dir`, output
root, external root, pinned admission-dir artifacts, cache scope, authorization
text, planner build argv / argv / env digests). `bootstrap_planner_v2_verify`
still prints the original line unchanged, then
`bootstrap-policy-error: planner-admission-v2-unbound-detail: binding=<b> expected=<e> actual=<a> verifier_root=<root> receipt=<path>`.
Any check that is not instrumented reports `binding=unclassified`. Every path
still returns 1.

## Specs

In `scripts/check/check-bootstrap-planner-admission-producer.shs --windows-smoke-env-only`:

- reproducing: a valid receipt verified against a second canonical root is
  refused, keeps the generic line, and the detail is exactly
  `binding=planner_source_path expected=<other>/src/... actual=<own>/src/... verifier_root=<other>`.
- generalization: a receipt whose `runtime_dir` is outside the verifier root is
  refused with `binding=runtime_dir expected=<root>/* actual=<dir>`.
