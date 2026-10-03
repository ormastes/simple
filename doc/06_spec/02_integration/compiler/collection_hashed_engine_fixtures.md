# Hashed collection engine fixtures

Authored acceptance programs for REQ-004/005, with exact sibling `.spl.expected`
markers. Neither execution nor measured scaling is claimed; requirements remain
open until admitted backend/runtime evidence exists.

| Existing runner filter | Production APIs and literal oracles |
|---|---|
| `collection_req004_` | `group_by_hashed` and `unique_hashed`: forced MIN-hash collisions, stable groups and first original records, empty input, seventeen-key growth with explicit ordered output |
| `collection_req005_` | Generic `HashMap`/`HashSet`: seventeen colliding integer entries, all retained values after growth, overwrite without count growth, present/absent removal, colliding text, tuple/enum sets, actual interned Symbol keys |

The Symbol case calls `Symbol.from` and checks identity from the existing runtime
interner; no synthetic integer wrapper stands in for a symbol. Its runtime and
import closure must be available. These tests call library implementations and
do not reproduce hash-table algorithms. Each main checks independent literal
results and returns nonzero before printing on mismatch; only full success emits
the exact marker. Seventeen-key input crosses initial capacity; it is a semantic
growth check, not an allocation or complexity measurement.

Use the existing `scripts/check/check_engine_differential.spl` discovery with
`DIFF_CERTIFY=1`, `DIFF_FILTER` from the table, and admitted pure-Simple binary
identity. Interpret/JIT/native use unchanged programs and oracles; native builds
explicitly request LLVM. JIT certification currently fails closed without a
production-owned execution witness. Native certification requires preadmitted
inventory and disables source-freeze fallback. Self-hosted/bootstrap-produced
artifacts describe compiler provenance, not new execution modes; the Rust seed
remains bootstrap-only. No runner or compiler was executed for this change.
