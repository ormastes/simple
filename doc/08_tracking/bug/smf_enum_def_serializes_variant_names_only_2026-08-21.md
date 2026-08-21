# SMF `EnumDef` serializes variant NAMES only — arity, types, field names and discriminants are dropped

- **Filed:** 2026-08-21
- **Status:** RESOLVED 2026-08-21 — struct + writer + reader landed atomically (enum record v2, GTPL header v2); see "Resolution" at the bottom
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

## Resolution (2026-08-21)

Landed as ONE change across the three files the record names:

| Layer | File | Change |
|---|---|---|
| struct | `src/compiler/10.frontend/ast.spl` `EnumDef` | 10 new trailing, defaulted fields: `variant_payload_counts: [i64]`, `variant_payload_kinds: [u8]` (0 unit / 1 tuple / 2 struct), `variant_payload_type_names: [text]` (flat), `variant_payload_field_names: [text]` (flat, parallel, `""` = positional), `variant_discriminants: [i64]`, `has_explicit_discriminant: [bool]`, `attribute_names: [text]`, `attribute_args: [text]` (`@closed` / `@evolving(repr:u16)` as HIR carries them), `complete_open: bool`, `dyn_open: bool`. Trailing + defaulted so every existing `EnumDef(...)` site (partition, subst, reader) keeps compiling — the seed fills partial named constructions positionally. |
| writer | `src/compiler/80.driver/smf_serialization.spl` | GTPL header version `1 -> 2`. `serialize_enum_placeholder` now emits **enum record v2**: 4-byte marker `ENV2` (`0x45 0x4E 0x56 0x32`), then the unchanged v1 body, then the ten fields above (`serialize_i64_list` = u32 count + 8-byte LE two's complement, `serialize_u8_list`, `serialize_bool_list`, text lists, two flag bytes). Also `serialize_text_field` used `text.to_bytes()`, which does not exist on either engine — switched to `.bytes()` (same call `smf_writer.spl` uses); the writer had never been executed by a spec. |
| reader | `src/compiler/40.mono/monomorphize/deferred_deserialize.spl` | `deserialize_enum_def` **refuses** any record without the `ENV2` marker: `deferred_set_error("SMF enum record ... is not format v2 (missing ENV2 marker): this .smf was written by an older compiler that serialized variant names only; rebuild it ...")` and returns nil — never reads v1 bytes as v2. The marker is the version gate because a v1 record begins with its u32 name length and `0x32564E45` (~845M) is not a plausible length, so the two layouts cannot collide. After reading the v2 block it checks the structural invariants (per-variant lists parallel to `variants`, flat lists sum to total arity, attribute lists parallel) and fails closed with a named error on each. Added `deserialize_last_error()` getter (module `var` was not importable into specs). Pre-existing enum `flags` read now returns nil at end-of-data instead of indexing past it. |

**Second defect found and fixed in the reader while writing the spec:** the whole
`deferred_deserialize.spl` file used `val r = read_x(...)` / `if r == nil: return nil` /
`r.0`, which the semantic checker rejects on both `test` (interpreter) and `run` (JIT)
with `invalid operation: tuple index access on non-tuple type enum` — i.e. no template
had ever been deserialized through this file on either engine. Every such site (58)
now force-unwraps after the nil check (`val r = r_opt!`), the idiom a probe confirmed
works (`match`/`!` pass, tuple-destructure of an optional does not).

**Evidence**

- `bin/simple test test/01_unit/compiler/linker/smf_enum_def_round_trip_spec.spl` —
  `Results: 15 total, 15 passed, 0 failed` (mirrored byte-identical at
  `test/unit/compiler/linker/`). Round-trip asserts arity, kinds, positional types,
  named field names/order with empty positional slots, discriminants incl. negative and
  >32-bit, `0` vs unspecified, `@closed`/`@evolving(repr:u16)`, `complete:`/`dyn:`,
  generic template bindings, and GTPL header byte `2`. Version skew: v1 names-only bytes
  (re-emitted exactly as the old writer did) -> nil + error naming `ENV2` and
  `older compiler`; non-parallel lists -> `not parallel`; arity mismatch -> `total arity`;
  truncated record -> `Unexpected end of data`.
- Pre-fix: the spec cannot even construct the fixture (fields absent) and the v1 reader
  accepted the v1 bytes as a well-formed payload-less enum — the exact silent loss.

**Still open (follow-ons, other lanes' files):**
- The *population* site (record point 4): nothing yet fills the new `EnumDef` fields
  from `decl_enum_def`'s parser lists / `HirEnum.attributes` / `complete_open` /
  `dyn_open` — the flat-AST bridge that builds `Node.Enum(EnumDef)` consumed by
  `partition_enum` (`40.mono/monomorphize/partition.spl:126`) is outside this change.
  Until it does, templates carry empty (but correctly versioned) metadata.
- `deferred_subst.spl` `_substitute_in_enum` builds a specialized `EnumDef` without
  copying the new fields (and should substitute type params inside
  `variant_payload_type_names`).
- `deferred.spl` `deserialize_templates` reads the GTPL header `version` and never checks
  it; the per-record marker is what gates today. A header check (`version != 2 ->
  error`) belongs there.
