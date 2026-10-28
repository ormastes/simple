# Native runner reports a resource limit with an empty limit kind

Canonical ID: `phase2_runner_empty_limit_classification_2026_10_28`
Status: OPEN; authoritative DB reconciliation pending.
Owner: native test-runner result transport/classification; cached phase2 compiler.

After the linked resource-scope shell-name workaround at `75a52c487ae`,
real children launch and all 11 native process/scope probes pass. The rebuilt
runner nevertheless reports `Resource limit exceeded ()` on normal file routes,
including positive, negative and empty BDD, SSpec and plain SPL inputs.
The empty limit kind conflicts with `run_scoped_child` deriving
`limit_exceeded` from `limit_type != ""`. The native reproduction below traces
the defect to tuple-match destructuring, not a real resource overrun.
Do not assume an actual budget overrun or bypass enforcement.

Reproduction and identities: sibling report
`phase2_resource_scope_shell_shadow_2026_10_28.md`, receipts under
`/tmp/runner-limit-shell-evidence-20261028/qualification-patched/`, especially
`spec_green_spec.spl.stdout`. It includes real child compiler output followed
by the empty-kind resource error. The MC/DC path also reports `struct i64 has
no field recorder` and explicitly falls back; this is a separate diagnostic.

Completed diagnostic: a minimal native caller of
`std.nogc_sync_mut.test_runner.native_owned_process.run_scoped_child` inspected
both `ProcessResult.limit_exceeded` and `limit_type` for exit 0, exit 7,
missing executable and a real timeout. The results below isolate tuple-match
transport while preserving scope enforcement and actual budget failures.
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
## Qualified workaround

The explicit tuple binding preserves the original `Ok`/`Err` match and early
error returns. The two production consumers now project typed `.0`/`.1` fields
before accessing the scoped result or evidence path. Compiler root repair is
still pending; the bug remains OPEN while the workaround is active.

The final nine-case native fixture passes: direct and wrapped normal exit 0,
exit 7, missing executable, real timeout, and the wrapper's error branch.
Each named PASS and the zero-failure summary is required by
`scripts/check/check-native-scoped-result.shs --binary <probe>`; a missing
binary is an error. The gate is explicitly manual because generic CI lacks
this producer-bound executable. Qualified fixture source: `bd79e2f7ae6`;
subsequent `c86c89e078d` changes only the production consumer placement, which
Luna identified and reviewed before the actual runner build.
Probe SHA256: `f09c60f2692c96dae81a3530ab1a9c5cd96a8f5c3b4b4ec32322410140ae397e`.

Producer SHA256: `0d6f2e4720845195c9f91de292056fac4c57cabef81390507c78d95e51133a28`.
No phase2 rebuild. Runner source: `c86c89e078d39417bcbc278271de63b8090c62f8`.
The runner builds in 191.765 seconds, peak observed process-tree RSS
7,388,368 KiB, quiescent completion. Runner SHA256:
`743224ffff9abc5842140f714c79a0b6c20cffeb8d4aaf034ac464f7b7334606`.

All 24 diagnostic acceptance invocations completed with the retained Phase1
child. BDD, SSpec and Markdown each return 0/1/1 for positive/negative/empty
inputs; positive BDD and SSpec execute one passing assertion, negative inputs
report the expected 41-versus-42 mismatch, and empty modules are rejected.
No invocation reports the former `Resource limit exceeded ()` error.
All negative and empty invocations return nonzero; no synthetic pass occurs.

Four source-documentation forms (`#`, `##`, `///`, docstring) retain correct
doctest subresults (green passes, red fails, empty rejected), but their whole
commands return 1 because the ordinary file route first rejects their empty
executable module. A standalone green SPL script executes but is rejected for
having no parseable test summary; its negative panic and empty inputs also
fail. These interpreter-route limitations are retained, not relabeled as full
format qualification. The existing MC/DC `struct i64 has no field recorder`
fallback remains visible. This mixed-producer runner is not promoted.

Exact identities, fixture hashes, rows and logs remain under
`/tmp/runner-limit-transport-evidence-20261028/`: `probe-check.stdout`,
`runner-build.status`, `runner-build.rss.env`, and
`qualification-patched/{identity.json,rows.json}`. Baseline and intermediate
probe receipts are preserved with `direct-`, `tuple-baseline-` and
`typed-match-` prefixes. Luna reviewed the corrected production placement;
range shell hygiene (17 fixtures), direct-env guards, and spec layout pass.
