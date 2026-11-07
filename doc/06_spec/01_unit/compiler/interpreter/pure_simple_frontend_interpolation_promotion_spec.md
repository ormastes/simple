# Pure-Simple Frontend Interpolation Promotion Specification

Status: **AUTHORED — AWAITING_VERIFICATION** (2026-11-07). This manual was
written from the executable source; it is not generated output or an execution
receipt. No runtime test or docgen command was run for this update.

Source: `test/01_unit/compiler/interpreter/pure_simple_frontend_interpolation_promotion_spec.spl`
at commit `b7b3845d2e0a6e0811638965be9b2ca902a9791d`;
SHA-256 `84805258b9750fd7b2bd3a69c820a0a7163994a077c2c9681ec5a061994e2b6c`.

The six examples drive `core_frontend_parse_reset` and inspect the resulting
AST. Fixture strings construct brace characters from character codes so the
host parsing the spec does not consume the syntax being tested. These assertions
cover frontend promotion and literal preservation; they do not execute the
resulting AST or establish native program output.

| Executable example | Expected assertion |
| --- | --- |
| Bare variable interpolation | Parsing succeeds and produces one interpolated-string node. |
| Expression and multiple regions | Parsing the two literals produces two interpolated-string nodes. |
| Brace-free literal | No interpolation node; at least one plain string node. |
| CSS-shaped region | Parsing succeeds without promoting the invalid expression region. |
| Nested literal region | The decoded literal equals the independently constructed `{spec: {maximumJournalEvents: 10000}}`; length is 37 bytes and bytes 35 and 36 both equal 125. |
| Intentional doubled escapes | No interpolation node; doubled outer braces decode to one pair around `literal`. |

The literal-byte checks distinguish preservation of rejected interpolation
regions from intentional `{{`/`}}` escape decoding. Node-count checks retain
coverage for valid interpolation. They must be evaluated together when changing
the frontend's no-placeholder branch.

Verification remains pending on a source-compatible pure-Simple full CLI and
runner with immutable compiler/runtime/source receipts. A minimal bootstrap
compiler alone cannot establish SSpec execution. Record actual executed and
skipped counts, failures, command identity, and generated manual provenance
when those commands are authorized. The separate 57-assertion-site native
`fill_span` extern diagnostic is neither execution of this spec nor compiler
admission.

See the published scoped prerequisites in
[Orchestrator verification wait](../../../../03_plan/sys_test/orchestrator_verification_wait_20261107.md). The retained defect evidence is
[Native nested SDN integer truncation](../../../../08_tracking/bug/native_nested_sdn_integer_truncation_2026_11_07.md).
All build and test tasks share the user's maximum of five CPU cores. This
authored update authorizes no bridge, provider build, or test launch.
