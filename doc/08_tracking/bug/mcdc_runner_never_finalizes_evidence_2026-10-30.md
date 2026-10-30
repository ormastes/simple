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
  - mcdc_instrument_clean_spec.spl (3 examples) -- file tagged `@tag:in-development`.
  To unblock: restore each skip() as `it "<name>": <body fn>()` (or drop the tag) and rerun.
- No longer red: mcdc_off_and_waiver_spec.spl "names the refusal in the output" is green since
  #5336 (refusal, exit 2).
  Related: mcdc_invalid_off_not_refused_mode_stays_off_2026-10-30.md
