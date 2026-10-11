# Platform-spec enum payload binding resolves the imported spec namespace

Date: 2026-10-11.
Status: observed Phase1 seed failure; scoped test-name workaround passed the
selected Phase1 seed rerun. No compiler fix is claimed.

## Evidence

`build/phase-one-ui-diagnostic/platform_spec_verification_spec/cycle-one.log`
records seven executed scenarios: six passed, one failed. The failure in
`should construct a composite enum carrying the complete nested specification`
prints an expected value containing the entire `std.spec` namespace instead of
the intended string `interpreter(remote(baremetal(riscv32)))`.

The pattern was `TestExecutionMode.Composite(spec)` inside a BDD `it` body.
The local binding should shadow an imported module name. This matches the
existing tracked defect:
`doc/08_tracking/bug/match_binding_shadowed_by_module_namespace_2026-08-18.md`,
with scope details in
`test/01_unit/language/match_binding_module_name_shadow_spec.spl`.

The producer and exact invocation are retained under
`build/phase-one-ui-diagnostic/platform_spec_verification_spec/`.
This is admitted Phase1 seed diagnostic evidence, not native acceptance.

## Bounded candidate

Rename only the local payload binding to `platform_text` and continue asserting
the full payload string. Keep the actual production Composite match and original
request unchanged. The candidate does not replace destructuring with a
string-only oracle and does not alter the six passing scenarios.

Do not use `Composite(val platform_text)` without parser support: the inspected
syntax guide uses bare payload bindings, and the current seed parser treats
`val` as a keyword used as an identifier/variant pattern, not an explicit
payload-binding modifier.

The renamed candidate passed the exact extracted failing scenario: 1/1 in
365 ms. Evidence is retained in
`build/phase-one-ui-diagnostic/platform-binding-cycle-two_spec/cycle-two.log`
and its receipts. The input manifest
`build/phase-one-ui-diagnostic/platform-daemon-cycle-two-inputs.json` binds
the canonical and selected spec inputs.

Together with the six unchanged baseline passes, all seven scenarios now have
passing diagnostic evidence across two attempts and two source snapshots.
The full file was not rerun after the rename; no single-run seven-case PASS,
native acceptance, or docgen validation is claimed. The broader compiler
namespace-precedence defect remains open. This failure does not demonstrate
a platform-spec parser defect.
