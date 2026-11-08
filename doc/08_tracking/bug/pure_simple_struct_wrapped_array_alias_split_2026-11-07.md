# pure-Simple: the core interpreter and MIR disagree on an array stored in a struct field

- **Found:** 2026-11-07 while measuring `seed_interp_call_root_shared_write_dropped_2026-11-07`.
- **Repro:**
  ```simple
  class Holder:
      arr: [i64]
  struct Wrap:
      items: [i64]
  val h = Holder(arr: [1, 2, 3])
  fn view() -> Wrap:
      Wrap(items: h.arr)
  fn main() -> i64:
      val w = view()
      w.items[0] = 50
      view().items[2] = 30
      h.arr[0] * 100 + h.arr[2]
  ```
- **Core interpreter (`core_interpret`):** returns 103. Building the struct copies the array, so neither write reaches `h.arr`. A plain local, by contrast, aliases: `var a = h.arr; a[2] = 70` changes `h.arr`.
- **MIR (in-process LLVM IR):** `rt_array_set` is called on the handle loaded from the struct field, which is the shared handle, so both writes reach `h.arr`.
- **Expected:** one pure-Simple semantics for an array stored in a struct field. This is an owner decision.
- **Status:** CLOSED-OBSOLETE (2026-11-08). The interpreter intentionally
  deep-copies value-struct fields and forks array descriptors at the value
  boundary (`eval_calls.spl:363-415`). This is the same value-type contract as
  the JIT's place-alias `rt_array_copy`; no unified write-through semantics is
  required.
