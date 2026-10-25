# Enum payload unit and empty tuple compatibility

Bug ID: `enum_payload_unit_empty_tuple_compatibility_2026_10_25`.
DB registration: **PENDING qualified full CLI or canonical BugDatabase API**.
Status: **SOURCE_FIX_CANDIDATE**; native verification remains pending; not closed.

The native enum constructor rejects unit arguments whose semantic type/carrier
is represented as Unit versus a zero-element tuple. Controls04 and controls05
report `payload type mismatch at 0` for UnitPayload.Pair/Separate at fixture47/48;
no native assertion ran.

Evidence: `/Users/ormastes/wt/release-phase2-review/build/verify/pattern-repair-native-controls-20261025-04/logs/unit_pattern_dispatch.compile.log` and
`/Users/ormastes/wt/release-phase2-review/build/verify/pattern-repair-native-controls-20261025-05/logs/unit_pattern_dispatch.compile.log`. Controls04 uses producer
`c2d1992b5a75adca9cb2bb735751ef6dafe67beb9489f4ff4dc51da375c0fd63` at source4bbdeead.
Diagnostic source `2a6c701f680160c5871ea14a190bab26bab9e102`; native producer `09037eaa61370ee3eeceb55156cc4ff01f6c136b5ce8014dd95742f733f9bf83`; source snapshot `53182ac596bbcc4fe01d28958dc1e8fb337a5d6f6db90445c39f16f5534ee3fb`. Gen13 runtime snapshot is `ecd1ed1cbf3f68a7abc6c2f852358542fae0b6e2e66c88e5abfcd5ea22cb3d2b`. Admission and publication were not attempted.

On merged source `64d0575f7b5e1b9219a6f09ab45ff5f1d042f79f`, the applied uncommitted
candidate changes `enum_payload_type_identity.spl` and
`enum_constructor_payload.spl`: accept typed Unit/empty-Tuple compatibility in
both HIR directions and MIR evidence, reject source Nil before that evidence,
and retain nonempty-tuple/other-type rejection. It does not broaden unrelated
nominal equivalence. New regression:
`test/01_unit/compiler/mir/enum_payload_unit_tuple_parity_spec.spl`.

This report records source review only. The new regression and native fixture
have not established this candidate's success. Keep this downstream type boundary
separate from source Unit-to-Nil bridging and anonymous tuple payload parsing.

Owner source SHA256 at `2a6c701f680160c5871ea14a190bab26bab9e102`:

- `src/compiler/50.mir/_MirLoweringExpr/enum_payload_type_identity.spl`: `dfff1a34059f2413908dd352d44946560be9b4e46615b2391620020313c81b9b`.
- `src/compiler/50.mir/_MirLoweringExpr/enum_constructor_payload.spl`: `26b7a2ceffe01cae0a165df4619208e2836bca84c56390a2767dcc786e79e934`.

Applied candidate source SHA256 when recorded (uncommitted, not a qualification):

- `src/compiler/50.mir/_MirLoweringExpr/enum_payload_type_identity.spl`: `d69fd8b66f492a9a09fccf440e895267a8361e9c24926be61ae3d67ce9d22518`.
- `src/compiler/50.mir/_MirLoweringExpr/enum_constructor_payload.spl`: `4e766072098bcc9c03f7bec1a5b810cc76e23fc927ed14d69152aba80ec2fb06`.

## Final candidate code reference

The candidate is now committed at `f70df57e8f45a0ff0c8f01745d221ec61e5d4f21`, including upstream `570fc936`, Unit/while/fiber correction `ab12acf89f6`, nested legacy-Nil hardening `1d7524a6375`, pinned-generation retention `b0caa844018` and diagnostic trace cleanup `f70df57e8f4`. Earlier uncommitted descriptions and hashes above are historical snapshots; all failed native04/05, SSA and cancelled-P3 evidence remains unchanged.

Status remains **SOURCE_FIX_CANDIDATE, native verification pending, not closed**. Recorded AST diagnostic success is limited to its stated producer and assertions. DB registration remains **PENDING qualified full CLI or canonical BugDatabase API**.

The recursive literal-Nil veto in `1d7524a6375` hardens the API-level legacy case where positive whole-Tuple type metadata masks a nested literal nil. Ordinary unannotated `Pair(nil, 7)` already rejects; this hardening does **not** establish a newly discovered ordinary-source acceptance bug. Preserve the separate Unit/empty-tuple compatibility root and its original native failures.

Current owner source SHA256 at the final candidate commit:

- `src/compiler/50.mir/_MirLoweringExpr/enum_payload_type_identity.spl`: `d69fd8b66f492a9a09fccf440e895267a8361e9c24926be61ae3d67ce9d22518`.
- `src/compiler/50.mir/_MirLoweringExpr/enum_constructor_payload.spl`: `53a5da2689af279d57c2fc3b37c578633f99d71c215a28e5295fc86e02e56f07`.
