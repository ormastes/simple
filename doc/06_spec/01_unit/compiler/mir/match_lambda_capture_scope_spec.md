# Match closure scope specification

Requirement: REQ-SSPEC-COMPILER. Bug: [mir_match_lambda_capture_scope_2026_10_17](../../../../08_tracking/bug/mir_match_lambda_capture_scope_2026_10_17.md).

Authored manual; execution and generated documentation **TEST_BLOCKED**. Source: `test/01_unit/compiler/mir/match_lambda_capture_scope_spec.spl`. No executed scenario count or PASS is claimed.

The twelve scenarios call the production pattern descriptor and MIR capture traversals. They check exact nested enum/tuple/array-rest/struct symbol sets; enum struct payloads; order-independent Or symbol sets; inconsistent/empty Or rejection; scrutinee and guard capture; arm shadowing; isolation between arms; outer-scope range endpoints; nested match scopes; literal-pattern dependencies and block statements without a value; invalid/unlowered pattern refusal; and unsupported expression refusal.

Expected outcome after qualification: all twelve registered scenarios pass with no skips. Invalid patterns must report unsupported scope and conservatively require capture analysis, ensuring they cannot bypass the existing refusal gate.

Run the unit command and native fixture recipe in the linked bug report using a compiler containing this patch. Exact-symbol tests establish scope analysis; the fixture separately establishes runtime values. Neither substitutes for the other.
