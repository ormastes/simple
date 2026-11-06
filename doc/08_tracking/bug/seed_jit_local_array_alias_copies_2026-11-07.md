# Seed JIT: a local bound to a field's array copies instead of aliasing

- **Found:** 2026-11-07 while measuring `seed_interp_call_root_shared_write_dropped_2026-11-07`.
- **Repro:**
  ```simple
  class Holder:
      arr: [i64]
  val h = Holder(arr: [1, 2, 3])
  fn main():
      var a = h.arr
      a[2] = 70
      print h.arr[2]     # pure-Simple core interpreter: 70; seed JIT: 3
  ```
- **Symptom:** pure-Simple treats arrays as shared handles, so the write is visible through `h.arr`. The seed JIT copies at the local binding, but writes through on `get_arr()[i] = v` and on `get_arr().push(x)`, so the same engine is not consistent with itself.
- **Expected:** pure-Simple semantics (write-through), consistently.
- **Status:** OPEN, not investigated further. Found alongside the call-root fix and deliberately kept out of it.
