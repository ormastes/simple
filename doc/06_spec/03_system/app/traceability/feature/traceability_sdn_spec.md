# Read an SDN traceability verdict

Manual companion to test/03_system/app/traceability/feature/traceability_sdn_spec.spl.
Requirements: REQ-TRC-001/007/010. AC002/015 coverage is partial.
Evidence: doc/09_report/traceability_cli_tdd_2026-10-11.md.

1. Inspect the tracked empty fixture through the real production command; decode
   the whole stdout with the shared strict typed codec and check canonical output,
   captured identity and completed structural scope with qualification=incomplete.
2. Request explicit SDN with dots; assert progress is on stderr.
3. Request quiet reporting; assert the verdict remains and stderr is empty.
4. Reject format, shorthand and log-mode JSON spellings with usage exit2 and no stdout.
5. Reject missing values, unsupported scope/format and unknown options before capture.
6. Read help; assert SDN/progress are documented and JSON is not advertised.
7. Select a missing file; assert infrastructure exit2, incomplete snapshot/evaluation,
   a parseable canonical report and a real diagnostic.

Actual source-staged Phase2 native result: seven examples, zero failures. Final
capture revisions are not covered by that earlier binary. Full dispatcher and
producer admission remain open. This manual is authored from executable steps;
no renderer, screenshot or generated-output admission is claimed.
