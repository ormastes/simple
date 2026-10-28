# Native runner reports a resource limit with an empty limit kind

Canonical ID: `phase2_runner_empty_limit_classification_2026_10_28`
Status: OPEN; authoritative DB reconciliation pending.
Owner: native test-runner result transport/classification; cached phase2 compiler.

After the linked resource-scope shell-name workaround at `75a52c487ae`,
real children launch and all 11 native process/scope probes pass. The rebuilt
runner nevertheless reports `Resource limit exceeded ()` on normal file routes,
including positive, negative and empty BDD, SSpec and plain SPL inputs.
The empty limit kind conflicts with `run_scoped_child` deriving
`limit_exceeded` from `limit_type != ""`; the owner is not yet proven.
Do not assume an actual budget overrun or bypass enforcement.

Reproduction and identities: sibling report
`phase2_resource_scope_shell_shadow_2026_10_28.md`, receipts under
`/tmp/runner-limit-shell-evidence-20261028/qualification-patched/`, especially
`spec_green_spec.spl.stdout`. It includes real child compiler output followed
by the empty-kind resource error. The MC/DC path also reports `struct i64 has
no field recorder` and explicitly falls back; this is a separate diagnostic.

Next diagnostic: compile a minimal native caller of
`std.nogc_sync_mut.test_runner.native_owned_process.run_scoped_child`, inspect
both `ProcessResult.limit_exceeded` and `limit_type` for exit 0, exit 7,
missing executable and a real timeout. Preserve scope enforcement and distinguish
nested-record transport, boolean comparison, and actual budget failures.
No runtime replacement or compiler rebuild is authorized by this report.

## Minimal native reproduction

At source `334f5c009cc`, direct `run_scoped_child` preserves normal exit 0,
exit 7, missing executable exit 126 and actual timeout classification. Both
nested and flattened `ProcessResult` booleans agree. Returning that result as
`Result<(ScopedChildRun, text), text>` and binding a match using tuple
destructuring instead corrupts all child fields into pointer integers.
The minimal probe's direct four cases PASS but wrapped exit-zero case FAILS.
Receipts and baseline source: `/tmp/runner-limit-transport-evidence-20261028/`
(`tuple-match-baseline.spl`, original `probe.stdout`).

Candidate workaround: typed tuple match result followed by typed `.0`/`.1`
projections. It preserves the Result error branch and does not alter limits.
Owning compiler defect remains open; no phase2 rebuild is performed.
Workaround qualification pending.
