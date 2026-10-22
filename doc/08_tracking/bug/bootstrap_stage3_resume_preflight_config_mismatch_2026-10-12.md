# Stage-3 resume preflight receipt can never verify: minter and verifier config strings disagree

Status: OPEN. Owner: bootstrap admission evidence.

## Defect

The authoritative preflight receipt that `--full-bootstrap` mints records a
configuration string that the managed Stage-3 resume verifier does not expect,
so `--resume-stage3-from-admitted` aborts at its stage2-verify step on every
host, independent of tree state.

- Minter (`scripts/bootstrap/bootstrap-from-scratch.sh`, full-bootstrap
  preflight step):
  `platform=<P>;backend=<B>;mode=<bootstrap_mode>;lane=full-bootstrap;cargo_profile=bootstrap;cargo_target=<triple>;cargo_features=<llvm feature flags>`
- Verifier (`scripts/bootstrap/resume-stage3-from-admitted.sh`):
  `platform=<P>;backend=<B>;mode=dynload;lane=full-bootstrap`

`check-bootstrap-preflight.shs --verify-receipt` compares the recorded
`config_hex` against `unpack("H*", EXPECTED_CONFIG)` by exact equality. The
verifier's expected string stops after `lane=full-bootstrap`; the minted
receipt always continues with `cargo_profile`, `cargo_target`, and
`cargo_features`. The comparison fails first, before any source/Git/seed
binding is reached, so the resume reports
`bootstrap-policy-error: admitted Stage 3 resume lacks current authoritative
preflight evidence` (exit 64) even for a freshly-minted, otherwise-valid
receipt on an untouched tree.

## Observed evidence (release_phase3 qualification, 2026-10-12, C:/p3)

Receipt `/c/p3/build/bootstrap/bootstrap-preflight.env` (minted by a passing
full-bootstrap preflight; `status=pass`, `cargo_mode=checked`) decodes:

```
platform=x86_64-pc-windows-msvc;backend=llvm;mode=dynload;lane=full-bootstrap;
cargo_profile=bootstrap;cargo_target=x86_64-pc-windows-msvc;
cargo_features=--features llvm
```

Resume command:
`bootstrap-windows.sh --strategy=adhoc --mode=dynload --no-mcp --jobs=1
--bootstrap-receipt=<planner-admission-v2.env>
--resume-stage3-from-admitted=build/bootstrap --output=build/bootstrap`

Result:
```
FAIL — authoritative preflight receipt rejected: /c/p3/build/bootstrap/bootstrap-preflight.env
bootstrap-policy-error: admitted Stage 3 resume lacks current authoritative preflight evidence
VERDICT — ABORTED: stage=stage2-verify exit=64 signal=none reason=stage2-verify
```

The two hex forms were recomputed by hand from the two scripts' literal format
strings and match the receipt/expectation respectively; they differ only by
the trailing `cargo_profile`/`cargo_target`/`cargo_features` fields.

## Suspected fix direction

Make the two owners emit one canonical config string: either the resume
verifier reconstructs the full minter form (it can read backend/mode from the
recorded stage2 transcript, but cargo profile/target/features are not recorded
there), or the minter stops at `lane=full-bootstrap` and records cargo
authority in separate receipt fields that verification checks independently
rather than inside the compared config blob. Until then the managed
"full-bootstrap → produce stage3 planner receipt → resume Stage 3" lane is
unreachable even though both halves work in isolation (the planner admission
producer itself passes end-to-end once the lane toolchain env — LLVM_HOME,
llc on PATH, MSVC LIB/INCLUDE, SIMPLE_WINDOWS_ABI=msvc, CC=clang-cl — is
provided).

## Related

- doc/08_tracking/bug/bootstrap_preflight_pass_not_retained_or_resume_bound_2026-09-21.md
  (the fixed parent issue: receipts now exist, verify, and bind; this bug is
  the config-content mismatch inside that working machinery).
- doc/08_tracking/bug/bootstrap_phase_verification_worker_exit_minus2_windows_2026-10-12.md
  (the separate matrix blocker that prevents reaching the receipt stage via a
  full stop-after-stage2 run on the qualification host).
