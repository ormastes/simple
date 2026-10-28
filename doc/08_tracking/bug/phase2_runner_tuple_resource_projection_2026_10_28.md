# Native runner resource fields after Result tuple extraction

The retained phase2 compiler can lose imported `ScopedChildRun` field layouts
when the value is extracted from `Result<(ScopedChildRun, text), text>`. Explicit
annotations on the tuple and child local preserve the result field but do not
preserve the nonzero offsets for `usage` and `budget_status`.

The existing native runner completed a passing BDD example, then SDN preflight
panicked in `resource_evidence_quality_name`. LLDB showed that
`run_scoped_child` returned valid resource evidence. In
`run_test_file_mcdc_interpreter_fallback`, however, both `child.usage` and
`child.budget_status` loaded offset zero, which holds `ProcessResult`. The
serializer received `Some(ProcessResult)` as `Some(ResourceUsage)`.

Diagnostic evidence: runner SHA-256
`bc2eecb9edcae539e7f4a3328ceff47152cda1ebd8a6e13e7545a23c3773c6be`.
Changing only the two AArch64 field loads at file offsets `0xb5038` and
`0xb50a4` from zero to 8 and 16 bytes allowed the identical spec-green SDN
invocation to complete with resource evidence intact. This binary patch was
only a causal experiment; it is not the implementation or a deployed binary.
The real child reported unavailable metrics, which remain explicitly
unavailable in its SDN record.

The source workaround projects these two fields through functions in the type's
owning module. All runner consumers, including limited child results, use that
boundary. No evidence is replaced with nil or synthesized zero metrics.
The underlying compiler layout defect remains open; remove the workaround only
after direct projections pass the same native fixture on a repaired compiler.

Regression fixture: `test/fixtures/test_runner_resource_projection/main.spl`.
It supplies distinct nonzero resource measurements, checks the enum names,
checks absent evidence, and checks the limited-result helper. Execute its native
binary with `scripts/check/check-native-resource-projection.shs --binary PATH`.
Use the selected pure-Simple compiler and runtime; an interpreter pass alone
cannot validate native field offsets.

Local diagnostic files are retained in `/tmp/sdn-producer-lldb.out`,
`/tmp/sdn-crash-lldb.out`, `/tmp/sdn-fallback.asm`, and
`/tmp/sdn-field-proof.stdout`. They are host-local evidence, not durable release
artifacts. The separate native SDN group-counter defect is outside this fix.

Validation: the retained pure-Simple compiler built the final native fixture in
132.1 seconds. The gate passed present, absent, and limited-result evidence.
Fixture binary SHA-256:
`2a7950ae5d930562571385e112b294f240bdb7e57ad6209a9771a2caf69e8ee9`.
The gate rejects an executable that exits zero without the regression summary;
a second negative control preserves both diagnostic streams and reports exit 7.
This validates the native projection boundary, not yet the entire rebuilt
runner or all SDN output formats.
