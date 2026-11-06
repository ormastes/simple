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
