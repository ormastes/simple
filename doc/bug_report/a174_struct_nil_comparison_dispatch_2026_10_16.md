# A174 struct nil-comparison dispatch (2026-10-16)

Status: pending bug database admission; generator-owned workaround candidate, native UNEXECUTED.

Retained pure-Simple A174 producer SHA256 a174b8e70b0a0ea4531db2ac5b8553f216590a7fbad0567cd9e40fd8e4630994 predates owner repair e458621e87670403385147dd4380acb0b925153d (retain presence semantics for struct nil comparisons). The newer source repair does not update that executable. Authority attempt3 retained224 generated hir_codec diagnostics on record ==nil/!=nil guards, reported as unresolved struct operator overloads. Example original lines4820 HirExpr,4827 Span; key-order66..68 SymbolId. Evidence: external phase3-validation-20261016/authority-attempt3-failure-table.md. Do not interpret224sites as224root causes.

Original A174 source/runtime inspection establishes record ExistsCheck emits rt_is_some and `not` uses lower_cond_operand; the three-cycle tiny native probe exhausted its attempts at SCV scope admission before semantic execution. Thus the proposed explicit presence expression is source-supported but NOT native-qualified.

Generator owner: src/app/compiler_schema/codec_gen.spl `_emit_enc` node/opaque branch. CodecUniverse.is_struct uses the authoritative struct/class declaration census; node enums are excluded. Emit `if not value.?:` only for concrete records and the two explicitly hand-coded opaque categories Expr/BlockValue. Keep enum comparisons and primitive/list/dict/optional/pair templates unchanged. No presence flag or encoded field is removed.

Mechanical generated sync (official generator unavailable): exact six-line 0/1 presence blocks were matched, encoder callee types resolved from generated function signatures plus explicit opaque signatures, and classified against the same nine declaration source paths. Changed343 record/opaque blocks; retained41 enum blocks. External record-nil-template-sync.json enumerates every original line/callee/type/value. This number includes all matching generated record blocks, beyond the224 retained diagnostics. No individual-site manual repair or production Python was added.

hir_codec_key_order changes only SymbolId left/right guards; scalar i64 special handling (including key3 negative oracle), text/list/dict and all other comparison logic remain unchanged.

Recovery reference is the actual compiler-owner source fix e458621e87670403385147dd4380acb0b925153d, not a claim that A174 contains it. Remove temporary syntax once a rebuilt producer verifies correct struct nil comparisons and codec round trips. Base source before workaround7b7a326cb5efbbbf0fc5426ae2b63f12e488f921; no automatic checkout/removal authorized.

Qualification: official generator regeneration/freshness UNRUN; native/interpreter tests UNRUN because no qualified runner was available. No fourth tiny probe or authority build. Root review required before candidate freeze. Existing codec nil/roundtrip/key-order fixtures remain authored evidence targets, not passing results. Enum comparisons and separate payload/constructor errors remain unresolved.
