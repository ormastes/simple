# Seed native-build: largest files hit the 300 s per-file timeout (2026-10-25)

## Symptom
Phase-ladder run 40155634904 (fresh phase 1 from `6002f1d155`), Rust seed
`native-build` of `src/app/cli/bootstrap_main.spl`, default `--timeout 300`:

| lane | file | result |
|---|---|---|
| linux-x86_64 | `src/compiler/20.hir/generated/hir_codec.spl` | timeout (300 s) |
| darwin-arm64 | `src/compiler/80.driver/driver_aot_native_output.spl` | timeout (300 s) |

Other files on the same runs took 282 s, 258 s, 237 s (linux) and 259 s,
231 s (darwin). One timeout makes the builder refuse every remaining
worker (`NOT_ATTEMPTED: previous native worker timed out; refusing
replacement admission`): 863 of 1532 files on linux, 394 on darwin. The
previous fresh run (40150810989, `14715d7e83`) passed on both lanes, so these
files are at the limit and the outcome depends on runner speed.
`hir_codec.spl` changed between the two runs (930b4959783, HIR codec v11).

## Workaround
`scripts/bootstrap/phase-ladder-step.shs` passes `--timeout 1200` to the seed
phase-1 build (`PHASE_LADDER_SEED_FILE_TIMEOUT` overrides). Compile speed is
unchanged; only the abort threshold moves.

## Open
Per-file seed compile time of the largest compiler files (~300 s on a hosted
runner) has not been profiled. Candidates: generated `hir_codec.spl` size, and
`driver_aot_native_output.spl` (single very large module).
