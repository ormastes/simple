# GUI Hardening Chrome/Corpus Evidence

Date: 2026-06-01

## Status

- overall=pass
- browser_corpus_specs=pass
- require_browser_corpus=1
- spec_timeout_seconds=180
- artifact_roots=doc/06_spec/system/wm_compare test/baselines/html_compat test/baselines/famous_site_corpus test/system/wm_compare/goldens
- artifact_restore_log=build/gui_hardening_open_gates_current/artifact-restore.log

## Browser/Corpus Specs

- test/system/wm_compare/backend_parity_spec.spl: status=pass duration_seconds=9 timeout_seconds=180 log=build/gui_hardening_open_gates_current/test_system_wm_compare_backend_parity_spec_spl.out
- test/system/wm_compare/browser_shell_parity_spec.spl: status=pass duration_seconds=9 timeout_seconds=180 log=build/gui_hardening_open_gates_current/test_system_wm_compare_browser_shell_parity_spec_spl.out
- test/system/wm_compare/electron_reference_parity_spec.spl: status=pass duration_seconds=10 timeout_seconds=180 log=build/gui_hardening_open_gates_current/test_system_wm_compare_electron_reference_parity_spec_spl.out
- test/system/wm_compare/html_compat_spec.spl: status=pass duration_seconds=9 timeout_seconds=180 log=build/gui_hardening_open_gates_current/test_system_wm_compare_html_compat_spec_spl.out
- test/system/wm_compare/golden_gate_spec.spl: status=pass duration_seconds=9 timeout_seconds=180 log=build/gui_hardening_open_gates_current/test_system_wm_compare_golden_gate_spec_spl.out
- test/system/wm_compare/famous_site_corpus_spec.spl: status=pass duration_seconds=97 timeout_seconds=180 log=build/gui_hardening_open_gates_current/test_system_wm_compare_famous_site_corpus_spec_spl.out

## Evidence Files

- Raw command output: build/gui_hardening_open_gates_current
- Artifact restore log: build/gui_hardening_open_gates_current/artifact-restore.log

## Policy

- Browser/corpus parity remains incomplete unless every listed SPipe spec passes.
- This wrapper intentionally evaluates only Chrome/corpus evidence.
