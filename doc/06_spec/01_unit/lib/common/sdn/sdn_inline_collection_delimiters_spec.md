# SDN Inline Collection Delimiter Integrity Specification

Status: **AUTHORED — AWAITING_VERIFICATION** (2026-11-07). This manual was
written from the executable source; it is not generated output or an execution
receipt. No runtime test or docgen command was run for this update.

Source: `test/01_unit/lib/common/sdn/sdn_inline_collection_delimiters_spec.spl`
at commit `b7b3845d2e0a6e0811638965be9b2ca902a9791d`;
SHA-256 `27661f7526ac7470946c5637878ac8fde0c28dcab858965ffaf470c9b56b72f6`.

The five examples exercise public `parse` and `parse_with_spans_and_issues`
entrypoints. They require a complete outer collection before delimiters are
removed, preventing malformed nested input from silently losing a numeric digit.

| Executable example and step | Expected assertion |
| --- | --- |
| Missing nested closers — Parse a nested mapping missing its outer closer | Missing map or array closers return `unterminated collection`, including input ending in `10000`. |
| Mismatched and extra closers — Check both delimiter types and trailing input | Wrong closer type returns `mismatched collection closer`; an extra closer returns `unexpected collection closer`. Trailing text and adjacent map/array roots return `text after collection`. |
| Complete nested integer — Parse an independently raw nested numeric document | Both public parse paths return exactly `10000` at `spec.maximumJournalEvents`. |
| Quoted delimiters — Keep quoted braces as data while validating the outer collection | The quoted `}]` stays scalar text and the neighbouring integer stays exactly `10000`. |
| Metadata entrypoint error — Ensure metadata collection cannot turn a parse error into success | An incomplete nested map returns `unterminated collection`; an unexpected success explicitly fails the example. |

Adjacent roots such as `[10000][2]` are invalid even though their final nesting
depth is zero: the first root already ended. Delimiters inside quoted values
do not affect collection depth. These checks preserve stable error messages
and cover both accepted input and malformed input; this spec does not assert
the contents of successful span or issue metadata.

Verification remains pending on a source-compatible pure-Simple full CLI and
runner with immutable compiler/runtime/source receipts. The companion native
fixture `test/fixtures/compiler/sdn_nested_literal_integrity.spl` remains a
separate pending literal-byte/integer regression. Neither source review nor
the independent 57-assertion-site `fill_span` extern diagnostic executes these
SSpec examples. Actual execution counts and generated manual provenance must
be recorded after authorized verification.

See the published scoped prerequisites in
[Orchestrator verification wait](../../../../../03_plan/sys_test/orchestrator_verification_wait_20261107.md). The retained defect evidence is
[Native nested SDN integer truncation](../../../../../08_tracking/bug/native_nested_sdn_integer_truncation_2026_11_07.md).
All build and test tasks share the user's maximum of five CPU cores. This
authored update authorizes no bridge, provider build, or test launch.
