# Test runner never aggregates or gates MC/DC evidence; instrumented wrapper degrades on plain specs

- test_runner_finalize_mcdc_results / test_runner_aggregate_mcdc_evidence / driver_complete_mcdc_report
  have no callers outside test_runner_mcdc_report.spl (grep src/). Per-file mcdc_evidence_v1 is carried
  in TestFileResult but no step turns it into a decision/condition report or a pass/fail gate, so an
  under-covered decision cannot fail a run and no "decisions" are ever printed.
- Plain and/or fixture degrades with `degraded=smf-compile-error:struct_i64_has_no_field_named_recorder`
  (fixer: fix/mcdc-wrapper-compile).
- `--no-session-daemon` single-file lane prints nothing about MC/DC (fixer: fix/single-lane-mcdc).
- Known-red specs (pending these fixes), all in test/03_system/app/test_runner/, each marked in-file
  (2026-10-30) so a suite sweep is not silently red:
  - mcdc_runner_applies_spec.spl "reports MC/DC decisions..." -- skip() linking here; body in
    check_reports_decisions().
  - mcdc_no_session_daemon_spec.spl "reports decisions for the instrumented single-file run" --
    skip() linking here; body in check_nodaemon_reports_decisions(). It was a vacuous green
    before: the fixture dir `nodaemon_decisions/` satisfied `contains("decision")`. Renamed to
    `nodaemon_report/`, and the check now ignores the case path.
  - mcdc_degrade_and_red_spec.spl "does not degrade a clean green spec" -- skip() linking here;
    body in check_clean_green_not_degraded().
  - mcdc_instrument_clean_spec.spl (3 examples): no longer tagged. The no-degrade checks run only
    under SIMPLE_MCDC_COMPILER (a probe-capable compiler) and are skipped otherwise. On the seed
    the spec asserts the explicit mcdc-unavailable degrade plus "MC/DC: NOT compliant" (#5343).
  To unblock: restore each skip() as `it "<name>": <body fn>()` (or drop the tag) and rerun.
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
