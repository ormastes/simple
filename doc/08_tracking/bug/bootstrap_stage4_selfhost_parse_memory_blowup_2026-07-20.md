# Stage-4 self-host full-CLI build: parse-phase memory blowup (~160MB/file, killed at 64GB)

- **ID:** bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20
- **Status:** OPEN
- **Severity:** high (blocks the stage3-compiled stage-4 lane entirely; seed-compiled fallback lane unaffected)
- **Lane:** bootstrap `--full-bootstrap --mode=one-binary --backend=cranelift`, x86_64-linux

## Symptom
When the stage-3 self-hosted binary compiles the full CLI (stage 4, `main.spl`,
1777 files), RSS grows ~160MB per parsed file and reached **64GB at 403/1777
files** before the repo `kill_monitor` terminated it. Extrapolated requirement
~280GB — not a tuning problem, a defect.

## Contrast (isolates the defect)
The seed-compiled stage-4 lane (`stage4_is_seed` fallback in the bootstrap
script) compiles the identical 1777-file closure with a **flat ~90MB RSS**
(observed 89-94MB throughout). The blowup is specific to the self-hosted
compiler's own parse/AST retention, not to the source set.

## Repro
Bootstrap run at b69e5469531 + stage-4 unblock fixes (landed 625c4ce97c7):
stage2 → stage3 (both PASS self-host sanity) → stage3 binary drives stage-4
full-CLI build → watch RSS in `build/bootstrap/logs/.../stage4-native-build.log`.

## Lead
Per-file arena/AST is apparently never released between files in the
self-hosted driver's multi-file loop (seed's Rust driver releases per file).
Suspect the stage-4 driver path holds every file's parse tree live for the
whole build.

## Workaround in force
Bootstrap script's own seed-compiled stage-4 fallback lane (which then hit its
own separate crash — see bootstrap_stage4_seed_compiled_full_cli_run_test_crash_2026-07-20).
