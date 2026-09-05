# SMF `EnumDef` serializes variant NAMES only — arity, types, field names and discriminants are dropped

- **Filed:** 2026-08-21
- **Status:** OPEN — recorded, deliberately NOT implemented in this lane
- **Severity:** medium (silent metadata loss across a module boundary)
- **Area:** `src/compiler/80.driver/smf_serialization.spl`,
  `src/compiler/40.mono/monomorphize/deferred_deserialize.spl`,
  `src/compiler/10.frontend/ast.spl`
- **Related lanes:** S1 (parser/HIR payload metadata,
  `test/01_unit/compiler/enum_payload/enum_payload_boundary_spec.spl`),
  S2 (MIR full-arity payload registry,
  `test/01_unit/compiler/mir/enum_payload/mir_enum_variant_payload_registry_spec.spl`)

## Symptom

An enum whose payload metadata survives the parser (S1) and MIR (S2) loses
that metadata again the moment it crosses an `.smf` boundary. For

```
enum E:
    A(i64, text)
    B(name: text, n: i64)
    C = 7
```

everything that reaches a consumer through SMF is the three strings
`["A", "B", "C"]`. Arity, positional types, named-field names, named-field
order and the explicit discriminant `7` are all absent — not corrupted, never
written.

## Root cause

`EnumDef` (`src/compiler/10.frontend/ast.spl:37-45`) declares

```
struct EnumDef:
    name: text
    generic_params: [text]
    variants: [text]          # <-- names only; no payload, no discriminant
    is_generic_template: bool
    has_specialization_of: bool
    specialization_of: text
    type_bindings: {text: text}
```

`serialize_enum_placeholder` (`smf_serialization.spl:267-291`) is faithful to
that struct — `buf = serialize_text_list(buf, enum_def.variants)` at line 281
is the whole variant payload of the format — and
`deserialize_enum_def` (`deferred_deserialize.spl:360`) reads it back
symmetrically. So the loss is in the AST TYPE, not in the codec: the codec
cannot write a field the struct does not have. Its own docstring, "Serialize a
full EnumDef including variants and bindings", is accurate about the struct and
misleading about the language construct.

Note this is a DIFFERENT layer from the two already-closed gaps. The parser now
carries payload metadata (`decl_enum_def`'s `variant_payload_types_flat` /
`variant_payload_counts` / `variant_payload_field_names_flat`), and HIR carries
`HirVariantKind.Tuple([HirType])` / `Struct([HirField])`. `EnumDef` is the
flat-AST placeholder used for deferred monomorphization and SMF template
storage, and it was never widened alongside them.

## Why it has not bitten loudly yet

Same-module compilation never round-trips through `serialize_enum_placeholder`,
and the MIR registry (S2) is populated from HIR directly. The exposure is
cross-module template instantiation and any consumer that reconstructs an enum
from a cached `.smf` rather than from source. Since a payload-less variant list
is structurally well-formed, the failure mode is a silent wrong answer
(unit-shaped variant, missing declared type, positional discriminant) rather
than a diagnostic.

## Format-change sketch (NOT implemented)

Deliberately mirrors the shape the parser already uses (`decl_enum_def`'s
flat parallel lists), so no new representation is invented:

1. **`EnumDef` gains four parallel-to-`variants` fields**

   ```
   variant_payload_counts: [i64]        # arity per variant, 0 = no payload
   variant_payload_kinds: [u8]          # 0=unit 1=tuple 2=struct, per variant
   variant_payload_type_names: [text]   # FLAT, cross-variant, source order
   variant_payload_field_names: [text]  # FLAT, parallel ELEMENT-FOR-ELEMENT
                                        # to variant_payload_type_names; "" for
                                        # positional slots
   variant_discriminants: [i64]         # resolved value per variant
   has_explicit_discriminant: [bool]    # so 0 != "unspecified"
   ```

   Payload types are serialized as their canonical type NAMES (text), not as
   symbol ids: an id is meaningless in the reading module, and the existing
   `struct_field_type_name` machinery in MIR already resolves cross-module
   types by name for exactly this reason.

2. **Codec, appended AFTER the existing fields** — `serialize_enum_placeholder`
   writes the six new lists following `serialize_text_dict(buf,
   enum_def.type_bindings)`; `deserialize_enum_def` reads them only when bytes
   remain. Appending keeps an old reader able to parse a new record's prefix.

3. **Version gate.** The append trick is not sufficient on its own — an old
   reader would silently produce the current lossy result and look fine. Bump
   the SMF section/format version so a reader that predates the change REFUSES
   a new record rather than half-reading it. Fail closed; a silently-lossy
   read is the exact defect being fixed.

4. **Populate at the one construction site** that lowers a parsed enum into
   `EnumDef`, from the parser lists that already carry all of this.

5. **Round-trip spec** under `test/01_unit/compiler/linker/`, alongside
   `smf_enums_spec.spl`: serialize the three-variant `E` above, deserialize,
   and assert arity/types/names/order/discriminant per variant — i.e. the same
   four properties S1 pinned at the parser boundary and S2 pinned at MIR, now
   pinned across the SMF boundary. A round-trip that only compares variant
   NAMES would pass today and must not be written that way.

## Not done here

This record exists so the gap is tracked rather than rediscovered. The lane
that filed it (S2) changed MIR only; nothing in `EnumDef` or the SMF codec was
touched, and `test/01_unit/compiler/linker/smf_enums_spec.spl` is green
(22/22) before and after that work.

## Not actioned 2026-08-21 — blocked by lane ownership, not by difficulty

Attempted in the interpreter/evaluation bug sweep and stopped before any
edit. The format change is a single atomic unit spanning three files:
`EnumDef` (`src/compiler/10.frontend/ast.spl`), the WRITER
(`serialize_enum_placeholder`, `src/compiler/80.driver/smf_serialization.spl`)
and the READER (`deserialize_enum_def`,
`src/compiler/40.mono/monomorphize/deferred_deserialize.spl`). This session
was fenced out of `src/compiler/80.driver` (owned by the concurrent bootstrap
lane), so only the struct and the reader could have been touched. Landing
those two without the writer produces exactly the failure mode the record's
point 3 warns about — a reader that expects fields no writer emits — which is
worse than the current honest lossiness. Deliberately left OPEN and
untouched; needs to be picked up by a lane that owns 80.driver, as one change.
