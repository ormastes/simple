# Bug: Dict<SymbolId, MirFunction> struct-key iteration yields only one entry (interpreter)

- **Date:** 2026-06-13
- **Severity:** P2 (silent data loss in iteration — masks multi-entry processing)
- **Status:** Open — NOT reproduced by isolated repros (2026-06-13); leading
  hypothesis (struct-key `to_key_string` collision) DISPROVEN. Needs the real
  `Dict<SymbolId, MirFunction>` build path to reproduce.
- **Area:** interpreter dict iteration with struct/composite keys

## Symptom

Iterating a `Dict<SymbolId, MirFunction>` (struct-typed key) in interpreter
mode yields only ONE entry even when several were inserted. Hit while
implementing the W3.1 kernel→VHDL bridge: a multi-kernel MIR module's kernel
dict iterated as if it held a single kernel.

## Workaround

Use a single-entry dict per processing step, or call the per-item function
directly for each known key (used in
`test/01_unit/compiler/codegen/vhdl_kernel_entity_contract_spec.spl`, which
calls `emit_vhdl_kernel_entity` once per kernel instead of iterating the
module dict).

## Expected

Dict iteration visits every inserted entry regardless of key type.

## Notes

Found during `doc/03_plan/language/gpu_fpga/sycl_parity_unified_kernel_plan_2026-06-13.md`
W3.1.

## Investigation 2026-06-13 — `to_key_string` hypothesis DISPROVEN

The original hypothesis was struct-key hashing/equality collision: the
interpreter keys dicts by `Value::to_key_string()`
(`compiler/src/value_impl.rs:84`), and composite keys (`Object`/`Tuple`/`Enum`)
fall through to the `other => format!("{other:?}")` arm. The theory was that
distinct struct keys render to the same string and collapse to one map slot.

**Disproven by three isolated repros, all interpreter mode, all printing the
correct count of 3 (no collapse):**
1. Module-scope `Dict<K, i64>` with `K { name: text }`, 3 distinct keys → `.keys()` = 3.
2. Dict as a struct field, populated via a `me`-method in sequence → `.keys()` = 3.
3. `Dict<Sym, Func>` with a struct *value* type and `Sym.new(name)` keys → both
   `.keys()` and `for k, v in d` = 3.

Reason the hypothesis fails: `Value` derives `Debug`, so `{other:?}` on an
`Object { class, fields }` renders the field values — distinct struct keys
already produce distinct key strings. `SymbolId` is `struct SymbolId: name: text`
(`src/compiler/00.common/dependency/visibility.spl:138`), a single-`text`-field
struct; distinct names ⇒ distinct keys.

**Where to look next (not yet done):** the defect must live in the real
`Dict<SymbolId, MirFunction>` build/iterate path, not in generic struct-key
dicts. Candidates: (a) `MirFunction`-value copy semantics during insert (dicts
may be value-typed like arrays — see the cross-module mutation-loss family);
(b) the specific MIR-lowering insertion path overwriting rather than inserting;
(c) upstream — the kernels may share an empty/identical `SymbolId.name` so the
collapse is correct dict behavior on a real key collision (a naming bug, not a
dict bug). Instrument the actual W3.1 code: print `module.functions` size
immediately after build, before iterating. Do NOT re-pursue `to_key_string`.
