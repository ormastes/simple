# Compound assignment through a getter/setter property fails on both seed engines

- **Found:** 2026-11-06 during W2a (assignment evaluation order). Data plan `doc/03_plan/compiler/data/data_attributes_layout_containers_xray_2026-11-06.md`.
- **Repro:**
  ```simple
  class Counter:
      raw: i64
  impl Counter:
      fn get_value() -> i64:
          self.raw
      me set_value(v: i64):
          self.raw = v
  fn main():
      var c = Counter(raw: 5)
      c.value += 2      # expected c.raw == 7
  ```
- **Seed interpreter:** `semantic: undefined field 'value'`. The augmented-field path never consults the getter/setter convention.
- **Seed JIT:** with `SIMPLE_JIT_STRICT=1`, the module is refused: `unresolved external symbol 'rt_field_set'`. Without strict mode the whole module silently falls back to the interpreter, which then fails as above.
- **Expected:** one getter read, then one setter write. Per the W2a contract the RHS runs first.
- **Status:** the same before and after PR #7260; it is not a regression from W2a.

## Resolution (2026-11-06)

- **Pure-Simple first:** `lower_accessor_write` (`src/compiler/20.hir/hir_lowering/_Expressions/accessor_forwarding.spl`) rejected every compound write through a forwarded accessor, as "seed parity", so no engine implemented the contract. All three engines now follow the owner contract and plan §591: the right-hand side first, then one getter read, then one setter write. A compound write with a setter but no `get_`/`is_` getter is still a hard error.
- **Pure-Simple HIR:** lowers to `{ val __accessor_rhs = rhs; recv.set_x(recv.get_x() op __accessor_rhs) }`. The receiver is a pure variable path, so naming it twice evaluates nothing twice.
- **Seed interpreter:** `exec_augmented_assignment` (`interpreter/node_exec.rs`) never consulted the getter/setter convention. The new `augmented_through_setter` reads through ordinary field access (getter forwarding) and writes through `forward_field_setter`.
- **Seed JIT (HIR):** setter forwarding in `hir/lower/stmt_lowering.rs` was limited to plain `=`. The compound form now binds the RHS to `$aug_rhs_N` and lowers `recv.set_x(recv.x op $aug_rhs_N)`, so `rt_field_set` is no longer emitted.
- **Evidence:** the `accessor_forwarding_spec.spl` compound cases (probe `probe_compound_setter.spl`) went from RED on both engines to GREEN on both engines, with JIT strict mode on. The new `accessor_setter_forwarding_spec.spl` case went from RED (`assign`) to GREEN (`block[let,method:set_kelvin/1]`).
