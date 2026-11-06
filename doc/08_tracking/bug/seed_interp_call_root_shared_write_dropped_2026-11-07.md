# Seed interpreter: a write through a call-result root over shared storage was dropped silently

- **Found:** 2026-11-07 in the review of PR #7297 (fix for `seed_interp_call_root_place_order_2026-11-06`).
- **Repro:** `test/01_unit/language/probe_call_root_shared_write.spl`. `get_arr()` returns `h.arr`, where `h` is a class instance holding an array field.
  ```simple
  get_arr()[0] = 9      # pure-Simple and seed JIT: h.arr[0] == 9
  get_arr()[1] += 5
  ```
- **Engines measured (2026-11-07).** The pure-Simple MIR row comes from reading the lowered LLVM IR in-process, not from running it.

  | Engine | `get_arr()[0] = 9` | `var a = h.arr; a[2] = 70` | `get_arr().push(4)` |
  |---|---|---|---|
  | pure-Simple core interpreter | writes through (9) | aliases (70) | writes through (len 4) |
  | pure-Simple MIR | `rt_array_set` on the returned handle (writes through) | — | — |
  | seed JIT | writes through (9) | copies (3) | writes through (len 4) |
  | seed interpreter, after PR #7297 | **dropped silently (1)** | copies (3) | dropped (len 3) |

- **Root cause:** in the seed tree-walking interpreter, arrays, dicts and structs are copy-on-write values: `Arc` plus `Arc::make_mut` (see the `interpreter/place.rs` header). PR #7297 bound the call result to a hidden local and wrote into it. When the result is still held elsewhere (refcount > 1), the write goes into a copy that is then dropped.
- **Fix (this change):** `place::refuse_shared_call_root` runs at the write, after RHS, root and indices have been evaluated in contract order. It walks every copy-on-write hop (Array, Dict, ByteArray, struct Object) from the bound call result to the written slot. If any hop is still held elsewhere (refcount > 1), it refuses with `call-result place root reaches storage that is still shared`. It stops at a ClassInstance, since that is shared and the write lands in it. A fresh result is a temporary on every engine and is still accepted.
- **Scope of the guarantee:** this covers call-result roots under an index projection (`call()[i]...`). Inline Tuple and FixedSizeArray values carry no refcount; they are value types and are not checked. `call().f = v` with no index goes through the field-assignment branch and does not use this path; it is not covered here.
- **pure-Simple's own split:** for `view().items[i] = v`, where `view()` builds a fresh struct whose field is the shared array, the core interpreter copies the array into the struct and so does not write through. The compiled MIR path calls `rt_array_set` on the shared handle and does write through. Because pure-Simple disagrees with itself, the seed interpreter refuses this shape too.
- **Remaining deviation (OPEN):** pure-Simple writes through, and so does the seed JIT; the seed interpreter now refuses. True write-through would require changing the seed interpreter's array value model, not one assignment path. The other rows in the table above (local alias and `get_arr().push`) are the same divergence and are still silent. That is tracked by `seed_jit_local_array_alias_copies_2026-11-07` for the JIT column and stays OPEN here for the interpreter.
- **Spec:** `test/01_unit/language/call_root_shared_write_spec.spl`. The pure-Simple and seed JIT cases are a characterization and were green on their first run. The seed interpreter case went from RED (the write was silently dropped, `shared_plain=1`) to GREEN (refused).
