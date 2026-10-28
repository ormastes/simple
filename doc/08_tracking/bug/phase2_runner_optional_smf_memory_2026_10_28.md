# Phase2 runner optional SMF cache exceeds memory cap

Status: OPEN; canonical BugDB registration PENDING, not registered.
Tracking tag: WORKAROUND-GNU-PHASE2-NATIVE-DIAGNOSTIC-20261028.

Producer SHA256: a757895813b3f6e31c31dead703ee4cd3e5434df75a138bfc7ad3ffed6a885fc.
GNU MinGW/Clang/LLD only. One build worker; 8 GiB reserve; 16 GiB RSS cap.
Evidence: `build/phase2-descendants-20261028/runner-extern-caller-cap16-final/`.

Native compile completed 292/292 modules; link completed 232/232 inputs.
Progress then entered `smf_package` at 0/292 without completing. The watchdog
reported exit 88 and peak RSS 16,798,996 KiB against cap 16,777,216 KiB.
The complete staged PE is 2,021,888 bytes, SHA256
2ab57f0dbae98c1dd33f46d75a87b0e52765ac6e8f59a00bab2f19b7b13c6a00.
Final atomic publication did not occur.

`driver_aot_pipeline.spl` handles Both by compiling native output first, then
calling `compile_to_smf` for a separate cache file. This cache is not embedded
in the PE. `driver_aot_smf_output.spl::collect_smf_bytes` is the next diagnostic
boundary; the precise allocation cause is not yet established. Expected:
bounded cache generation or an explicit supported native-only output policy
that preserves honest admission and cache semantics.

The tagged workaround is inspection of a private copy only, under
`build/phase2-native-only-diagnostic/a757895813b3f6e3/`. PE headers/hash were
verified. Execution starts but `--help` exits 1 with `unknown option: --help`;
this is not a passing functional runner test. Never promote this copy as an
admitted artifact. Remove the diagnostic workaround when the normal build,
publication and real runner checks pass. Owner: compiler driver/SMF cache.

The bounded repair campaign is stopped. New SPL specs, fullCLI/core/MCP smoke,
and production readiness remain unverified. PR stays draft. The malformed
canonical BugDB and missing real writer block registration; no database edits
or stub-writer success are claimed.

## Source investigation, 2026-10-29

Landing status update: PR #5153 was merged into `release/1.0.0` on
2026-10-28 at 05:58:11 UTC, merge commit
`c0c1e5a37b7f64a7562c3936d9b2b519568c0e6c`.
The earlier draft/HOLD description above records the investigation's prior
state; merging does not establish the missing runner or production checks.

The retained descendant command supplies `--entry` but omits `--mode`.
The full native-build worker defaults to `dynload`;
`src/app/cli/native_build_output_plan.spl::native_build_output_format_v1`
selects Both for that mode when neither explicit native-only output nor a
native group is requested. `--mode one-binary` selects Native when
`--emit-smf` is absent. The assignment to Native on bootstrap_main's
positional source route does not establish the explicit-entry worker's policy.

This provides a supported native-only diagnostic command without changing
compiler defaults, disabling the memory guard, or introducing MSVC settings.
Prepared local helper:
`build/shared-scheduler-evidence/build_phase2_native_only_prepared.sh`.
It adds `--mode one-binary` to the retained GNU command and preserves the
14 GiB cap, 8 GiB reserve, one worker, producer hash check, and fresh-output
requirement. It has NOT been executed: the prior repair campaign's retry
budget is exhausted. No build, runner, admission, or memory-improvement PASS
is claimed. The SMF collector also rejects COFF only after compiling and
concatenating modules; early format validation remains a separate proposed
repair, not an established cause of the measured allocation peak.
