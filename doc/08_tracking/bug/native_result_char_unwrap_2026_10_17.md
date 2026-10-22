# Native Result<char,text>.unwrap is unsupported

Date: 2026-10-17
Bug: BUG-NATIVE-RESULT-CHAR-UNWRAP-20261017
Database registration: pending; no admitted database tool available.
Status: OPEN producer limitation; source workaround proposed, cycle2 UNRUN.
Intended-code recovery:29ef54b368901bc27116320b57e13576c85db36c.

Exact0CD6 NativeChar feature cycle1 reached MIR97/97 modules:96 succeeded,1 failed. The only fatal is unicode_scalar_char_fixture.spl:7:27, unsupported Result unwrap payload type, at converted.unwrap() for actual Result<char,text>. Both complete worker stderr logs and the coordinator log remain preserved with SHA256 in external unicode-scalar-native-char-cycle1/terminal-failure-receipt.json. No native candidate was executed and no successful primitive qualification is claimed.

Source owner: src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl lower_result_unwrap_core selects supported payload kinds but has no Char arm, so its unsupported-result diagnostic fires. This is separate from generator prim_text and unsupported character-literal expressions. It is not evidence that validated numeric-to-char cast failed.

The temporary fixture workaround matches the actual returned Result with Ok/Err, binds the success payload through an explicit char local and retains every numeric cast-back, actual HirExprKind.CharLit construction/match, scalar and rendering-byte assertion. The Err arm returns the real reason. All boundary and high-bit invalid controls remain unchanged. Existing unwrap_err for text remains supported and is retained. The public helper's doctest checks its successful is_ok result instead of falsely implying char.unwrap works; doctest execution remains UNRUN. Public implementation, return contract and scalar guards are unchanged.

Source evidence: switch_operators_calls.spl enum-match binding3915 invokes decode_declared_enum_payload_slot; enum_constructor_payload.spl:311 lowers the declared payload type and remembers its HIR owner. enum_payload_value:644 preserves Char through its raw-word default rather than an integer tag shift. The raw MIR carrier can remain i64, which is why the explicit char binding and strict actual CharLit payload admission must remain in the genuine next native control; no runtime success is inferred from source shape alone.

The immediately preceding workaround tag identifies this bug and full recovery hash. Applied workaround commit is recorded in external cycle2 freeze metadata after commit. Removing the workaround requires fixing and qualifying the actual producer unwrap owner, not just fetching a patch. No automatic recovery/reset is authorized.

Next attempt is NativeChar feature cycle2/3, SAME entry and cycle1 persistent cache with ordinary source invalidation, same exact producer/runtime/SDK lineage. Root must review frozen source/command before launch. No stale cache identity rewrite, foreign runtime, reader helper rerun, generated-codec consumer claim or exhausted-budget reset is permitted. Broad compiler/lib/MCP/LSP/BDD and whole-codec acceptance remain UNRUN.