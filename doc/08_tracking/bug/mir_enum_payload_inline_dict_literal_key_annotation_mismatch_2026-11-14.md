# MIR rejects inline `SdnValue.Dict({...})` literal: "enum payload dictionary key annotation mismatch"

Bug ID: `mir_enum_payload_inline_dict_literal_key_annotation_mismatch_2026-11-14`
Severity: P2. Status: open. Layer: `50.mir` (pure-Simple MIR lowering).

## Symptom

The frozen Windows Phase 2 pure-Simple compiler fails MIR lowering for an enum
constructor whose payload is a dict literal written inline:

```simple
SdnValue.Dict({"kind": SdnValue.String("x"), "version": SdnValue.Int(1)})
```

with `MIR lowering error: enum payload dictionary key annotation mismatch`
(and a companion `enum construction 'lib.common.sdn.value.SdnValue.Dict':
payload type mismatch at 0`). The declared payload is `Dict(Dict<text, SdnValue>)`
(`src/lib/common/sdn/value.spl:35`) and every key is a plain `text` literal, so
the construction is type-correct. The Rust seed accepts it.

Observed in the llm_caret native-build (diag-phase4 lane, log
`/c/dev/wt-lane2/build/diag-phase4/q_caret/build.log` and
`.../crt1_caret/build.log`) for 5 modules.

## Location

`src/compiler/50.mir/_MirLoweringExpr/enum_constructor_payload.spl:311-312`,
`lower_declared_enum_payload_expression`, `HirTypeKind.Dict` arm:

```simple
if annotated_key != None and not enum_payload_types_alias_compatible(key_type, annotated_key, self.symbols):
    self.error_fatal("enum payload dictionary key annotation mismatch", Some(expression.span))
```

The HIR `DictLit` key annotation is documented in that file as "nullable
despite its historic non-optional field declaration". Inspection lead (not a
demonstrated root cause): for an unannotated literal the synthesized key
annotation, or the `!= None` test on a non-Option-typed field in the
natively compiled compiler, is not the "no annotation" case, so a synthesized
key type is compared against `text` and rejected.

## Workaround (source, behaviour-preserving)

Bind the literal to a typed local first, so the payload expression is a
variable rather than a `DictLit`:

```simple
val fields: Dict<text, SdnValue> = {"kind": SdnValue.String("x"), "version": SdnValue.Int(1)}
SdnValue.Dict(fields)
```

Sites carrying `# @workaround bug=mir_enum_payload_inline_dict_literal_key_annotation_mismatch_2026-11-14`
(landed in PR #9022):

- `src/lib/nogc_async_mut/container/providers/linux/engine_policy_v1.spl` (3 sites)
- `src/lib/nogc_async_mut/container/providers/linux/request_codec_v1.spl`
- `src/lib/nogc_async_mut/container/providers/windows/docker_exec_control_probe_v3.spl`
- `src/lib/nogc_async_mut/container/providers/linux/containment_observer_v1.spl`
- `src/lib/nogc_async_mut/container/providers/linux/installed_containment_policy_v1.spl`

Many other container provider files already use the typed-local shape
(e.g. `user_mapping_v3.spl`, `docker_exec_claim_v3.spl`); they were written
that way and are not tagged.

Known untouched instance of the failing shape (not in the llm_caret closure,
so it has not failed a build yet):
`src/lib/nogc_sync_mut/orchestration/host_service_peer_policy_v2.spl:59`
(`rules.push(SdnValue.Dict({"peerUid": ...}))`).

## Fix / removal

Fix the key-annotation check so an unannotated (or synthesized) `DictLit` key
annotation is treated as absent, or compare by alias-equality against the
declared `text`. Then remove the tagged workarounds and confirm the inline
form lowers in a native-build of `src/app/llm_caret/main.spl`.

## Root cause and fix (2026-11-14, seed-interpreted pure-Simple MIR; native proof pending)

Demonstrated, not the `!= None` hypothesis above: since `9bb344bb1cf` (2026-10-21) HIR writes
`HirType(kind: HirTypeKind.Infer(0, 0))` as the key type of EVERY dict literal
(`src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl`, `ExprKind.DictLit`:
"Infer(0, 0) denotes an unannotated type"). The MIR check predates that (`aad6de3fe10`,
2026-10-10) and treated any non-None key as an ascription, so `text` was compared against
`Infer` and every inline dict literal payload was refused.

Fix: `enum_payload_dict_key_is_ascribed` in `enum_constructor_payload.spl` — an `Infer` key
is no ascription. The literal then goes to `lower_dict_lit` with the declared key and value
types, which still refuses a wrong key (`{1: 2}` into `Dict<text, i64>`: "enum payload
dictionary key type mismatch") and a wrong value ("... value type mismatch").

Evidence (seed, pure-Simple HIR + MIR): `contextual_enum_payload_spec.spl` 19 of 25 before,
24 of 25 after (the five dict cases); `enum_payload_local_evidence_spec.spl` covers the
accept / wrong-key / wrong-value cases and the settled-ascription refusals. NOT yet shown on
a natively built compiler, so the tagged workarounds stay; remove them after a Phase 2
binary built from this change lowers the inline form.
