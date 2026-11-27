# Anonymous tuple enum payload parsing gap

Bug ID: `enum_positional_anonymous_tuple_payload_parse_gap_2026_10_25`.
DB registration: **PENDING qualified full CLI or canonical BugDatabase API**.
Status: **SOURCE_FIX_CANDIDATE and AST_DIAGNOSTIC_PASS**; native verification remains pending; not closed.

The enum payload lookahead failed to route an LPAREN-starting positional tuple
type through positional payload parsing. `Nested((i64,text))` must retain one
payload type whose kind is Tuple with two children, alongside unchanged named
and array payload neighbors.

Owner: `src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl`.
Commit `2a6c701f680160c5871ea14a190bab26bab9e102` adds that lookahead case.
Regression: `test/01_unit/compiler/frontend/tuple_payload_unit_parity_spec.spl`.

The normal Rust DDD interpreter (`ddd5aa4b9c47433ac814983d7499002a115e9f0e28f4623bfe26dba7e6b0a714`) ran the installed structural fixture at source `2a6c701`: **1 executed, 1 passed, 0 failed/skipped**, exit0, quiescent. The fixture SHA256 was `a482ac8899b8af51f6665715cf6558e44edc286ea1fcd51aabfd27863492d057`. This is parser/AST diagnostic evidence, not native carrier or Phase2 qualification.

Evidence: `/Users/ormastes/wt/bootstrap-pattern-provenance-20261025/build/verify/tuple-unit-structural-interpreter-20261025-01/logs/spec.log` and `/Users/ormastes/wt/bootstrap-pattern-provenance-20261025/build/verify/tuple-unit-structural-interpreter-20261025-01/receipts/inputs.before.env`.
Controls04 with producerc2d199/source4bbdeead and controls05 with producer09037/source2a6c701
both failed the native unit-payload fixture at MIR payload compatibility. Those
failures are not an isolated native test of this parser correction.
Diagnostic source `2a6c701f680160c5871ea14a190bab26bab9e102`; native producer `09037eaa61370ee3eeceb55156cc4ff01f6c136b5ce8014dd95742f733f9bf83`; source snapshot `53182ac596bbcc4fe01d28958dc1e8fb337a5d6f6db90445c39f16f5534ee3fb`. Gen13 runtime snapshot is `ecd1ed1cbf3f68a7abc6c2f852358542fae0b6e2e66c88e5abfcd5ea22cb3d2b`. Admission and publication were not attempted.

Keep the original failures in `/Users/ormastes/wt/release-phase2-review/build/verify/pattern-repair-native-controls-20261025-04/logs/unit_pattern_dispatch.compile.log`
and `/Users/ormastes/wt/release-phase2-review/build/verify/pattern-repair-native-controls-20261025-05/logs/unit_pattern_dispatch.compile.log`. Native acceptance remains
pending after the distinct Unit/empty-tuple compatibility boundary is repaired.

Owner source SHA256 at `2a6c701f680160c5871ea14a190bab26bab9e102`:

- `src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl`: `83506e6eb510ccfb59f2d9f2c4b9c1d2fec115a2a6aa715b0a1ba31efbf874d9`.

## Final candidate code reference

The candidate is now committed at `f70df57e8f45a0ff0c8f01745d221ec61e5d4f21`, including upstream `570fc936`, Unit/while/fiber correction `ab12acf89f6`, nested legacy-Nil hardening `1d7524a6375`, pinned-generation retention `b0caa844018` and diagnostic trace cleanup `f70df57e8f4`. Earlier uncommitted descriptions and hashes above are historical snapshots; all failed native04/05, SSA and cancelled-P3 evidence remains unchanged.

Status remains **SOURCE_FIX_CANDIDATE, native verification pending, not closed**. Recorded AST diagnostic success is limited to its stated producer and assertions. DB registration remains **PENDING qualified full CLI or canonical BugDatabase API**.

Current owner source SHA256 at the final candidate commit:

- `src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl`: `83506e6eb510ccfb59f2d9f2c4b9c1d2fec115a2a6aa715b0a1ba31efbf874d9`.
