# Test runner never aggregates or gates MC/DC evidence; instrumented wrapper degrades on plain specs

- test_runner_finalize_mcdc_results / test_runner_aggregate_mcdc_evidence / driver_complete_mcdc_report
  have no callers outside test_runner_mcdc_report.spl (grep src/). Per-file mcdc_evidence_v1 is carried
  in TestFileResult but no step turns it into a decision/condition report or a pass/fail gate, so an
  under-covered decision cannot fail a run and no "decisions" are ever printed.
- Plain and/or fixture degrades with `degraded=smf-compile-error:struct_i64_has_no_field_named_recorder`
  (fixer: fix/mcdc-wrapper-compile).
- `--no-session-daemon` single-file lane prints nothing about MC/DC (fixer: fix/single-lane-mcdc).
- Gated (2026-10-30, user decision): every former red example (runner_applies "reports MC/DC
  decisions", no_session_daemon "reports decisions", degrade_and_red "does not degrade a clean
  green spec", and the 3 instrument_clean shapes) now runs as a real example only when
  SIMPLE_MCDC_COMPILER names a probe-capable compiler (same gate as
  mcdc_real_instrumentation_spec, #5355), and is skipped with that reason otherwise. Under the
  Rust seed, a sibling example asserts the explicit mcdc-unavailable:compiler-lacks-probe-emission
  degrade (#5343) and, in the directory lane, "MC/DC: NOT compliant". The no_session_daemon
  fixture dir is `nodaemon_report/` (it used to be `nodaemon_decisions/`, which made the check
  vacuous).
- No longer red: mcdc_off_and_waiver_spec.spl "names the refusal in the output" is green since
  #5336 (refusal, exit 2).
  Related: mcdc_invalid_off_not_refused_mode_stays_off_2026-10-30.md

## Status 2026-10-30
- FIXED: the analyzer never found a pair. mcdc_mask_word discarded its true/masked match (#5344).
- FIXED: the aggregate dropped the evidence-loss and strong-coupling classifications (#5345).
- FIXED: end-of-run aggregation and report. `test_runner_mcdc_run_gate` (test_runner_mcdc_report.spl) runs in both lanes.
  - Degraded files and files with no evidence are listed and counted as NOT COMPLIANT, but the test verdict is unchanged (user ruling: the Rust seed emits no probes).
  - A run fails only when real evidence is present, the profile is normal or stricter, and the gate rejects it.
  - Specs: test/01_unit/app/test_runner_mcdc_run_gate_spec.spl, test_runner_mcdc_transport_spec.spl, test/01_unit/lib/mcdc_analyzer_spec.spl.
- OPEN: mcdc_runner_applies "reports MC/DC decisions" and mcdc_degrade_and_red "does not degrade a clean green spec" are still red. The plain fixture degrades (`struct i64 has no field recorder`; fix/mcdc-wrapper-compile), and the Rust seed cannot emit probes.
- OPEN (found by Fable review of #5345): a `strong_coupling=true` obligation can still be accepted as covered-masking. `analyze_mcdc_with_context_bounded` gets no policy table, so a formal context whose own strong_coupling is false can produce masking coverage. In analyze_mcdc_one_decision, strong coupling forbids masking. Fixing this changes behaviour and needs an owner decision.
- OPEN: `--profile=dev` on the `--no-session-daemon` lane still resolves MC/DC as required (mode=on).
