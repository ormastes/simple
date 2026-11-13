# Seed: an engine demotion re-runs `main()`, duplicating its side effects

- Date: 2026-11-13. Lane `work/spy-xray-2-20261113`.
- Binary: Rust seed `src/compiler_rust/target/bootstrap/simple` (sha256 `df9dfb057afb7b8f…`).

## Observation

`simple run test/fixtures/xray/xray_win64_twin_dump.spl` (two `print` lines in `main`) printed
each `TWIN-TEXT` / `TWIN-XDATA` line TWICE. The run log shows
`[engine-demotion] reason=hybrid-interp-splice detail=spl_f64_to_bits` between the copies:
the program's `main` ran on the first engine, the engine was demoted, and `main` ran again on
the next one. Every side effect before the demotion point is repeated (prints here; a file
write, a patch or a network call elsewhere).

## Impact

Any caller that parses stdout or relies on exactly-once effects is wrong under the seed.
`scripts/check/check-xray-native-win64-objects.shs` takes the first occurrence (`head -1`) as
a stop-gap; that masks the symptom, it does not fix it.

## Next step

Demotion must happen before any user code runs, or the demoted run must resume rather than
restart. Repro: `XRAY_WIN64_REL32=0 <seed> run test/fixtures/xray/xray_win64_twin_dump.spl | grep -c TWIN-TEXT`
(expected 1, observed 2).
