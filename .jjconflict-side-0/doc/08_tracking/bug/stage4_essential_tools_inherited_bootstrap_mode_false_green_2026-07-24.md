# Stage 4 essential-tools probes inherited bootstrap mode

Status: SOURCE-FIXED; fresh Stage 4 execution remains pending.

## Bug

`bootstrap-from-scratch.sh` exports `SIMPLE_BOOTSTRAP=1` and points
`SIMPLE_RUNTIME_PATH` at the Rust bootstrap runtime. The essential-tools smoke
cleared bootstrap mode for binary identity only, so the test-runner, lint,
duplicate-check, and JSON validation probes could exercise bootstrap-only
compiler or runtime semantics while claiming production readiness.

## Root fix

`check-bootstrap-essential-tools-smoke.shs` now clears `SIMPLE_BOOTSTRAP` and
`SIMPLE_RUNTIME_PATH` at the shared `run_probe` boundary and for the standalone JSON validator.
`stage4_smoke_gate_spec.spl` requires both execution paths to retain that
production-mode boundary.

## Remaining qualification

Run the essential-tools smoke once through the next fresh incremental Stage 4
CLI. Source-contract success is not Stage 4 runtime qualification.
