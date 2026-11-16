# Node attribute layouts (language spec)

A **node attribute** is a named, typed field of a tree node (for example the
compiler AST `extra`, `s_val` and `op` slots) whose storage is chosen
separately from the node's own record. You use one read/write/presence/retire
API (`AttributeStoreV1<T>`, in `src/compiler/00.common/data/attribute_schema_v1.spl`),
and the **backing layout** behind it is chosen once, when the store is built.
After that, each access switches on the `AttrPlacementV1` enum tag. It never
compares a string.

## Backing layouts

| Token | `AttrPlacementV1` | Where the value lives | Status |
|---|---|---|---|
| `direct` | `Embedded` | on the main node, through an `AttrOwnerV1<T>` owner delegate | supported (default) |
| `column` | `Column` | a side array indexed implicitly by node id | supported |
| `array_index` | `ArrayIndex` | a compact side array; the node holds the slot index (`AttrOwnerV1<i64>` index owner); retired slots are reused | supported |
| `sparse_hash` | `SparseHash` | a hash side table keyed by node id | supported |
| `array_ptr` | `ArrayPointer` | the node holds a pointer to a side-array slot | **fails fast** |
| `hash_ptr` | `HashPointer` | the node holds a pointer to a hash entry | **fails fast** |

`array_ptr` and `hash_ptr` are recognised as tokens. Building a store with
either one returns `Err` that names the reason: safe Simple has no element
reference that stays valid when the side array grows or the hash rehashes.
`&T`, `*T` and `-T` are not enforced through `bin/simple`, and
`slots.push(...)` replaces the array. The supported equivalents are
`array_index` (a stable slot index) and `sparse_hash`. Supporting real
pointer layouts is tracked by `TODO(node-attr-pointer-layouts)` in
`attribute_schema_v1.spl` (picked up by `bin/simple todo-scan`).

Detached stores (`attr_store_detached_v1`) own their values. Column,
array_index and sparse_hash all have a detached form; for a detached
array_index store the per-node slot index is held in an internal
`AttrIndexCellsV1`. Use `attr_store_indexed_v1(attr, index_owner)` when the
slot index should live on the node itself.

## Data layout: AoS and SoA

`AttrLayoutV1` selects how a **multi-field** side array is laid out:

- `aos`: array of structs. One interleaved array; field `f` of row `r` is at
  `r * nfields + f`.
- `soa`: struct of arrays. One array per field. This is the default, and it
  is the layout every single-field column already has.

`attr_group_store_v1<T>(attr, placement, nfields, layout)` builds an
`AttrGroupStoreV1<T>`. A row is the node id for `column` and the node-held
slot for `array_index`. AoS and SoA apply only to layouts that have a side
array, so `direct`, `sparse_hash`, `array_ptr` and `hash_ptr` return `Err`.
A single-field store answers identically in both layouts.

## Switches

All switches are default OFF. With them off, behaviour is identical to having
no node-attribute support.

| Switch | Meaning |
|---|---|
| `SIMPLE_NODE_ATTR="extra=<tok>,s_val=<tok>,op=<tok>,layout=<aos\|soa>"` | per-attribute backing layout and side-array data layout |
| `SIMPLE_NODE_ATTR_SDN=<file>` | `data_policy.rules` layout rows, resolved by `data_attr_storage_resolve_v1`; the env override wins |
| `SIMPLE_NODE_ATTR_COUNT=1` | access counters |

An unknown or unsupported token (including `array_ptr` / `hash_ptr`) turns
every attribute back to `direct` and resets `layout` to `soa`. Each
non-direct placement must pass a round-trip self-check before it is used. If
the check fails, the attribute stays on `direct`.
`expr_attr_side_layout()` reports the selected data layout.

## Verification

- `test/01_unit/compiler/data/attribute_layouts_spec.spl`: every layout ×
  AoS/SoA, read/write round-trip, growth and rehash, slot reuse, pointer
  layouts failing fast.
- `test/01_unit/compiler/data/attribute_schema_v1_spec.spl`: the original
  three-placement parity checks.
- `test/02_integration/compiler/data/ast_attr_apply_spec.spl`: the real AST
  with the switch off (the off-identity fingerprint), with array_index, and
  with `layout=`.
