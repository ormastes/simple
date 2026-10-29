# Native AOT suite requests retired terminal JSON

Baseline: release/1.0.0 `17c632ff6a0`. Status: source fix and host contract tests
verified; current pure-Simple native execution remains blocked by the missing
pinned P2 producer and host provider prerequisites.

`run-native-aot-suite.shs` invoked `--json` while the current runner supports
text/doc/SDN output. `validate-native-aot-evidence.pl` then required exactly
one terminal JSON result. The documented supported text route could never
satisfy this validator. SDN has additional scoped-environment V4 requirements
and is not an available bypass for a missing native host owner.

The wrapper now selects `--format text`. The validator reads exact current
per-file PASS lines and one exact aggregate Results line, cross-checks the
suite inventory, actual native invocation records, compiler/runtime options,
execution records and executable image identities, and retains failed
artifacts. Pending/skipped/cached or malformed verdicts, duplicate summaries,
retired JSON and mismatched counts fail closed. The existing explicit JSON
invocation wire record is preserved; it is not a terminal result format.

Five new unittest methods cover 41 fixture cases. Before the fix, the two
backend text controls failed with `expected exactly one terminal JSON result`
and the wrapper-control test found `--json`. All five methods pass after the
fix. The existing shell evidence-contract suite was migrated to text; its
scratch directory now uses a physical path so macOS symlink aliases do not
contradict the private-artifact identity check. Perl/shell syntax checks pass.

These fixtures use synthetic transcript and image bytes to test the gate.
They do not compile or run Simple, prove native assertions or authenticate
the transcript. Run current-source native SSpec with an admitted surviving
producer before claiming end-to-end qualification. No Phase 2 rebuild occurred.
Other historical phase wrappers still using terminal JSON need their own
protocol migration and tests; this scoped repair does not qualify them.

Reproduce:

```sh
python3 -m unittest discover -s test/01_unit/scripts -p native_aot_suite_contract_test.py -v
sh test/01_unit/scripts/bootstrap_native_aot_evidence_contract_test.shs
```

The [end-to-end plan](../../03_plan/sys_test/buildrunner_sosix_end_to_end_2026_10_29.md)
records dependencies, host failure matrices and remaining acceptance evidence.
