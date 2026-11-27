# FlatAst unit expression becomes nil

Bug ID: `flatast_unit_expression_bridged_as_nil_2026_10_25`.
DB registration: **PENDING qualified full CLI or canonical BugDatabase API**.
Status: **SOURCE_FIX_CANDIDATE and AST_DIAGNOSTIC_PASS**; native verification remains pending; not closed.

The FlatAst expression bridge fell through from source Unit to nil. Source `()`
must become an empty `ExprKind.TupleLit`; source `nil` must remain `NilLit`.
This distinction is needed before nominal/enum payload compatibility is checked.

Owner: `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`.
Commit `2a6c701f680160c5871ea14a190bab26bab9e102` separates the Unit branch.
The exact source bytes are retained by the source2a6c701 guard03 snapshot; the
structural fixture checks both function-body AST forms.

The normal Rust DDD interpreter (`ddd5aa4b9c47433ac814983d7499002a115e9f0e28f4623bfe26dba7e6b0a714`) ran the installed structural fixture at source `2a6c701`: **1 executed, 1 passed, 0 failed/skipped**, exit0, quiescent. The fixture SHA256 was `a482ac8899b8af51f6665715cf6558e44edc286ea1fcd51aabfd27863492d057`. This is parser/AST diagnostic evidence, not native carrier or Phase2 qualification.

Raw evidence: `/Users/ormastes/wt/bootstrap-pattern-provenance-20261025/build/verify/tuple-unit-structural-interpreter-20261025-01/logs/spec.log` and its canonical RSS/identity receipts.
Native controls05 still fails UnitPayload.Pair/Separate construction before
execution at a later typed compatibility boundary. Preserve
`/Users/ormastes/wt/release-phase2-review/build/verify/pattern-repair-native-controls-20261025-05/logs/unit_pattern_dispatch.compile.log`.
Diagnostic source `2a6c701f680160c5871ea14a190bab26bab9e102`; native producer `09037eaa61370ee3eeceb55156cc4ff01f6c136b5ce8014dd95742f733f9bf83`; source snapshot `53182ac596bbcc4fe01d28958dc1e8fb337a5d6f6db90445c39f16f5534ee3fb`. Gen13 runtime snapshot is `ecd1ed1cbf3f68a7abc6c2f852358542fae0b6e2e66c88e5abfcd5ea22cb3d2b`. Admission and publication were not attempted.

No native success or full compiler qualification follows from the AST result.
The UI lowercase-unit nominal alias report is a different owner and is not reused.

Owner source SHA256 at `2a6c701f680160c5871ea14a190bab26bab9e102`:

- `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`: `b6b2a23c41b7fbbbb2b188d64b2066d453763630b8160599036c22cb6ad771c1`.

## Final candidate code reference

The candidate is now committed at `f70df57e8f45a0ff0c8f01745d221ec61e5d4f21`, including upstream `570fc936`, Unit/while/fiber correction `ab12acf89f6`, nested legacy-Nil hardening `1d7524a6375`, pinned-generation retention `b0caa844018` and diagnostic trace cleanup `f70df57e8f4`. Earlier uncommitted descriptions and hashes above are historical snapshots; all failed native04/05, SSA and cancelled-P3 evidence remains unchanged.

Status remains **SOURCE_FIX_CANDIDATE, native verification pending, not closed**. Recorded AST diagnostic success is limited to its stated producer and assertions. DB registration remains **PENDING qualified full CLI or canonical BugDatabase API**.

Current owner source SHA256 at the final candidate commit:

- `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`: `b8c18e4f26a887c6cacbcc570997380c39aae0cdfd0110be7e52d48752fdaa1b`.
