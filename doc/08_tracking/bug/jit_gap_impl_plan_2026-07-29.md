# JIT Gap Implementation Plan — 2026-07-29

**ANALYSIS/DESIGN ONLY.** No source was edited, nothing was built, nothing was
committed. This turns `jit_gap_reaudit_2026-07-29.md` +
`jit_dispatch_worklist_2026-07-29.md`'s two blocked classes (Object/Enum print
metadata; the 37-43 NEEDS-RUNTIME methods) into turnkey specs. All line numbers
are from a static read on 2026-07-29 and should be re-verified before landing —
this is a design doc, not a patch.

---

## Part A — runtime name-metadata for Object/Enum print

### Current state (confirmed by source read, not just the print stub)

`src/compiler_rust/runtime/src/value/sffi/io_print.rs::heap_value_to_display_string`
has the two stub arms the reaudit measured:

```rust
HeapObjectType::Object => format!("<object@{ptr:p}>"),   // line 551
HeapObjectType::Enum   => format!("<enum@{ptr:p}>"),      // line 553
```

But the reaudit's bonus row shows JIT actually prints `<invalid-heap:0x...>`
for a class instance, **not** `<object@ptr>` — i.e. it never even reaches line
551. Tracing why revealed two structurally different problems, not one:

### Finding 1 — Enum: the header is fine, only the name lookup is missing (SMALL)

Enum construction goes through the real runtime constructor:
`codegen/instr/pattern.rs::compile_enum_unit`/`compile_enum_with` call
`rt_enum_new(enum_id, discriminant, payload)`
(`runtime/src/value/objects.rs:271-288`), which correctly writes
`HeapHeader::new(HeapObjectType::Enum, size)` plus `enum_id`/`discriminant`/
`payload`. So `v.heap_type()` succeeds and `<enum@ptr>` is genuinely reached —
this is a **pure missing-name-table** gap, nothing structural is broken.

The **names are already known at codegen time** and are being computed away:
`MirInst::EnumUnit { dest, enum_name: String, variant_name: String }` and
`EnumWith { .., enum_name, variant_name, payload }`
(`mir/inst_enum.rs:549-567`) carry the full string names into codegen. The
dispatch arms (`codegen/instr/mod.rs:980-995`, mirrored in
`codegen/llvm/functions.rs:1407,1445`) convert those names to numeric IDs via:

- `codegen::shared::enum_runtime_type_id(enum_name)` (`codegen/shared.rs:21-36`)
  — reserves 0=`Result`, 1=`Option`, else a 32-bit FNV-style hash of the name.
- `codegen::instr::pattern::calculate_variant_discriminant(variant_name)`
  (`codegen/instr/pattern.rs:128-134`) — low 32 bits of Rust's `DefaultHasher`.

**Both are hashes, not dense compiler-assigned IDs, and both have a
documented collision** — `codegen/shared.rs:224-233`'s own test asserts
`enum_runtime_type_id("collision.Type175882") == enum_runtime_type_id("collision.Type255081")`.
A name table keyed on these IDs inherits that collision risk (two different
enum types could show the wrong name in the rare colliding case) — acceptable
for a display fallback, but must be documented, not silently assumed unique.

`rt_enum_id` (the `enum_id` accessor) **already exists** and is already
re-exported (`runtime/src/value/mod.rs:232`) — no new accessor needed for the
enum_id side.

**Smallest mechanism (Enum):**
1. During lowering/codegen, accumulate every distinct `(enum_name, variant_name)`
   pair seen at `EnumUnit`/`EnumWith` sites into a compile-time set, hashed the
   same way construction hashes them (so lookup keys match).
2. Emit that set once as linked data — reuse the **exact existing mechanism**
   already used for struct vtables: `declare_data(..., Linkage::Export)` /
   `Linkage::Import` (`codegen/instr/mod.rs:819-834`) — just for a name table
   instead of a vtable, so this is a copy of an established pattern, not new
   plumbing.
3. Add two new runtime accessors that read that injected table at runtime:
   `rt_enum_type_name(enum_id: u32) -> RuntimeValue(text)`,
   `rt_enum_variant_name(enum_id: u32, discriminant: u32) -> RuntimeValue(text)`.
   Fall back to `<enum:ID/DISC>` on a miss (never panic on a hash collision).
4. `io_print.rs`'s Enum arm becomes: read `enum_id` (`rt_enum_id`, exists) and
   `discriminant` (`rt_enum_discriminant`, exists), look up both names, format
   `"{type_name}::{variant_name}"` for a unit variant or
   `"{type_name}::{variant_name}({})"` recursing `value_to_display_string` on
   `rt_enum_payload(v)` for a payload variant — matching the interpreter's
   `Color::Green` / `Option::Some(5)` shape exactly.

**Estimated size: 2 new runtime functions + 1 emitted data table (copy of an
existing pattern) + ~10-line io_print.rs edit. Genuinely small.**

### Finding 2 — Object: there is no header at all under JIT (BIGGER than the guide assumed)

Grepping every call site of `rt_object_new` across the whole compiler
(`codegen/`, `mir/lower/`) turns up **zero call sites** — it is only ever
called from Rust unit tests (`object_tests.rs`, `dict.rs` tests,
`equality.rs` tests, `collection_tests.rs`). It is registered in the runtime
import table (`codegen/runtime_sffi.rs:519`) but **never invoked by either
codegen backend's actual struct-construction path**.

What both backends do instead (`codegen/instr/closures_structs.rs::compile_struct_init`
lines 298-340, and the LLVM mirror `codegen/llvm/functions/objects.rs::compile_struct_init`
lines 15-90+, whose own comment says "matching Cranelift behavior"):
1. `rt_alloc(struct_size [+ 8 if a vtable ptr is prepended])` — a bare
   allocation, not `rt_object_new`.
2. Store the vtable pointer at offset 0 if applicable, then store each field
   at its byte offset — direct memory writes, no `HeapHeader`.
3. Tag the low bit: `let tagged_ptr = ptr | 1` (`closures_structs.rs:337-338`)
   — the same generic "this is a heap pointer" bit shared with arrays/strings,
   but **no `HeapObjectType` discriminant is ever written**.

So a JIT-built struct instance has no `HeapHeader`, no `class_id`, no
`field_count` — `v.heap_type()` in `io_print.rs` cannot decode a type tag from
it at all, which is *exactly* why the reaudit measured `<invalid-heap:0x...>`
instead of even `<object@ptr>`. `rt_object_new`/`rt_object_field_get`/
`rt_object_field_count`/`rt_object_class_id` are fully implemented and unit
tested in Rust (`runtime/src/value/objects.rs:90-155`) but are **dead code
from codegen's perspective** — this is a real, separate structural bug, not
a naming-metadata gap.

**Where the names live at compile time (and where they're dropped):**
`mir/lower/lowering_expr_struct.rs::lower_struct_init_expr` (lines 9-155)
resolves `type_name` via `self.type_registry.get_type_name(ty)` and threads it
into `MirInst::StructInit { type_id, struct_name: Option<String>, .. }` (line
146) — the **type name already survives to codegen**. Field *names*
specifically do not: `type_registry.get(ty)` returns
`HirType::Struct { fields: Vec<(String, TypeId)> }` (line 111-115), but the
lowering only keeps `field_types`/`field_offsets`/`field_values` — the field
name half of that tuple is discarded on the spot (line 115:
`.map(|(_, ty)| *ty)`).

**Two implementation options, ranked by risk:**

- **Option A (recommended, lower risk) — out-of-band registration, no layout
  change.** Assign every distinct `struct_name` a dense compiler-assigned
  `class_id` (a fresh counter — **not** the existing `TypeId`, which is
  documented to collide across modules per-`TypeIdAllocator`; see the
  `codegen/instr/mod.rs:800-818` comment about `SoftwareBackend`/
  `BaremetalBackend` both landing on `TypeId(155)`). Add one new runtime call,
  `rt_object_register_class(ptr, class_id)`, invoked once right after
  `rt_alloc` in `compile_struct_init` (both backends) — no change to
  `struct_size`, `field_offsets`, or any existing FieldGet/FieldSet math. The
  runtime keeps a `HashMap<*const u8, ClassId>` (safe only if allocations are
  pointer-stable for their lifetime — true for this `rt_alloc`-based,
  non-moving model; confirm no relocating GC exists before relying on this).
  Print does `rt_object_lookup_class(ptr) -> class_id -> name table` (table
  emitted the same way as Finding 1's enum table, this time also carrying
  `field_names: Vec<String>` per class, sourced by adding a `field_names`
  member to `MirInst::StructInit` fed from the currently-dropped
  `lowering_expr_struct.rs:115` tuple). **Blast radius: construction + print
  only.**
- **Option B (bigger, higher risk) — prepend a real header.** Extend
  `compile_struct_init` to write a `class_id` word ahead of the fields (the
  same "+8 and shift all field_offsets" pattern already used for the vtable
  pointer at `codegen/instr/mod.rs:836-849`), and update every FieldGet/
  FieldSet consumer's offset math (`effective_field_offset`,
  `codegen/instr/mod.rs:863+`) to account for it. This is closer to "real"
  `rt_object_new` parity but touches the layout of **every struct in every
  compiled program**, not just print — must be validated against the whole
  struct/method-call suite, not just a print probe. Flag as the fallback if
  Option A's pointer-stability assumption turns out false.

**Estimated size: this is the "big" half.** Not because names are hard to find
(they're one dropped tuple field away), but because JIT struct instances
currently have zero runtime type identity at all — Option A is a scoped,
new-code-only fix (one new runtime call + one new table + one dropped-field
restore); Option B is a real ABI change. Recommend Option A.

### File overlaps with the method-dispatch files (sequencing)

- **`codegen/llvm/functions.rs`** — confirmed overlap. This file holds the
  `EnumUnit`/`EnumWith` match arms (~line 1407, 1445) that Finding 1 touches,
  and is also the LLVM backend's general instruction dispatcher, so any
  Part B LLVM-side NEEDS-CODEGEN fix (dict.set/insert, text.reverse/clear/
  push/pop, etc., if landed on the LLVM path) lands in the same file. Land
  Part A's Enum-table change first (it only touches the Enum arms) to avoid a
  same-`match`-block merge race with Part B's dict/text arms.
- **`codegen/instr/closures_structs.rs`** — confirmed direct overlap.
  `compile_struct_init` (Part A's Object work) and `compile_method_call_static`
  (the general method-dispatch entry point) are in the **same file**, one
  function apart (lines 298 and 366). Any Part B batch whose dispatch arm
  lands here must be sequenced against Part A's Object-header change.
- **`lowering_expr_method.rs`** — no overlap found. Part A's construction
  paths run through `lowering_expr_struct.rs` / `lowering_expr_call.rs` /
  `mir/inst_enum.rs` instead; this file is the one Part B's dispatch-arm work
  is expected to land in. Low collision risk with Part A, but **not
  independently re-verified for EnumUnit/StructInit HIR-level matching** —
  grep it before touching, this pass did not walk the HIR stage.
- **`hir/lower/expr/mod.rs`** — not touched by any call chain this pass
  walked (Part A's chain starts one stage later, at MIR lowering). Flag as
  unverified rather than confirmed-clear.

### Part A verdict

**Enum = small fix** (2 new runtime fns + 1 reused emission pattern + a
10-line print edit). **Object = bigger fix** — not a naming problem but a
missing-runtime-identity problem; Option A above scopes it back down to
"one new runtime call + one new table + restore one dropped field," which is
still materially more than Enum's fix but far short of a struct-layout
rewrite.

---

## Part B — NEEDS-RUNTIME method specs (batched)

### Count reconciliation

The reaudit (`jit_gap_reaudit_2026-07-29.md`) re-confirmed **37** methods as
NEEDS-RUNTIME (unchanged from the worklist, no backing `rt_*` symbol, all
still `Function '...' not found`): array (6) `ndim/chunk/compact/rotate/
fetch/transpose`, dict (6) `merge/clone/compact/fetch/setdefault/dig`, text
(25) `capitalize/swapcase/title/trim_start_matches/trim_end_matches/
removeprefix/removesuffix/chomp/squeeze/reversed/push_str/partition/
rpartition/replace_first/repeat/pad_start/pad_end/center/zfill/is_numeric/
is_alpha/is_digit/is_alphanumeric/is_whitespace/find_all`. The guide's "43"
also names `array.remove` and `text.reverse` — those are re-classified in the
reaudit as **NEEDS-CODEGEN** (an arm exists and compiles but is wired to a
no-op/wrong value, not "not found"), so 37 + 2 = **39** distinct methods are
covered below, not 43; the extra 4 could not be traced to a specific named
method in either source doc and are treated as the guide rounding up from a
pre-reaudit count. `array.remove` and `text.reverse` are listed as a
dependency note in Batch 5, not full NEEDS-RUNTIME batch members, since their
real fix is the shared "text/array mutability wired wrong" root-cause the
reaudit's #3 priority item already flags — implementing new `rt_*` symbols
for them would be wasted work if that root-cause fix lands first.

### Compose-from-existing vs new-logic, by re-reading the actual runtime export list

A fresh grep of every `pub extern "C" fn rt_{string,array,dict}_*` actually
implemented in `runtime/src/value/` (not just the worklist's static claim)
confirms none of the 37 target names exist yet, but many can be **composed**
from primitives that already exist and are already used by other landed
fixes (`rt_string_chars`, `rt_string_join`, `rt_array_reversed`/`sorted`,
`rt_array_drop`/`take`, `rt_dict_keys`/`values`/`set`/`contains`,
`rt_string_char_code_at`, `rt_array_all_truthy`, etc.) — this revises the
worklist's blanket "no cheap composition" note downward for several methods.
"Compose" below means *no new Rust runtime symbol*, but still needs a new
codegen dispatch arm and (per Part B's own finding) a new entry in
`codegen/runtime_sffi.rs`'s `RuntimeFuncSpec` table for any not-yet-imported
existing symbol it calls (`rt_array_drop`/`take`/`all_truthy` etc. are not
currently in that table's `RuntimeFuncSpec::new(...)` list, confirmed by a
literal-pattern grep — a fresh full read of the file is needed before
implementing, this grep may have missed entries added via a different call
style).

**The codegen import-table / declaration site (`resolve_runtime_func`'s
source of truth):** `codegen/instr/helpers.rs:303`'s `resolve_runtime_func`
reads `ctx.runtime_funcs`, which is populated in
`codegen/common_backend.rs:1272` (`self.runtime_funcs.insert(spec.name, id)`)
from `codegen::runtime_sffi::runtime_funcs_for_target()` — i.e. **every**
runtime symbol a dispatch arm calls via `call_runtime_N` must have a
`RuntimeFuncSpec::new(name, params, returns)` entry in
`src/compiler_rust/compiler/src/codegen/runtime_sffi.rs`. This is true
whether the underlying Rust function is brand-new or already exists and is
merely unimported by codegen — new-symbol and compose-only methods both need
a `runtime_sffi.rs` entry for any not-yet-declared call.

### Batch table

| method | receiver | rt_ symbol | compose? | files to touch | batch# |
|---|---|---|---|---|---|
| `ndim` | array | `rt_array_ndim` (new) | new-logic | `runtime/src/value/array_ext.rs` (new), `codegen/runtime_sffi.rs`, `lowering_expr_method.rs`, `codegen/instr/collections.rs` | 1 |
| `chunk` | array | `rt_array_chunk` (new) | new-logic | same as above | 1 |
| `compact` | array | none — filter-nil via `rt_array_filter`-style predicate | compose (needs predicate wiring) | same as above | 1 |
| `rotate` | array | none — `concat(drop(arr,n), take(arr,n))` | compose (`rt_array_drop`+`rt_array_take` exist, need `runtime_sffi.rs` entries + a concat) | same as above | 1 |
| `fetch` | array | none — `get` + bounds check + default at lowering | compose (may not need NEEDS-RUNTIME reclass at all) | same as above | 1 |
| `transpose` | array | `rt_array_transpose` (new) | new-logic | same as above | 1 |
| `merge` | dict | none — loop `keys`/`values`/`set` | compose | `lowering_expr_method.rs`, `codegen/instr/collections.rs` (no new runtime file needed unless a loop-free single-call version is preferred) | 2 |
| `clone` | dict | none — loop `keys`/`values`/`new`/`set` | compose | same | 2 |
| `compact` | dict | none — loop `keys`/`values`, skip nil, `set` | compose | same | 2 |
| `fetch` | dict | none — `contains`+`get`+default | compose | same | 2 |
| `setdefault` | dict | none — `contains` guard + `set` | compose | same | 2 |
| `dig` | dict | `rt_dict_dig` (new, only if variadic path is needed) | new-logic if variadic; compose if key-list is static/unrollable | same + `runtime/src/value/dict_ext.rs` (new) if new-logic path chosen | 2 |
| `capitalize` | text | none — `char_at(0)`+`to_upper`+`substring(1..)`+`to_lower`+`concat` | compose | `lowering_expr_method.rs`, `codegen/instr/methods.rs` | 3 |
| `swapcase` | text | `rt_string_swapcase` (new — per-char scan) | new-logic | `runtime/src/value/text_case_ext.rs` (new), `codegen/runtime_sffi.rs`, `lowering_expr_method.rs`, `codegen/instr/methods.rs` | 3 |
| `title` | text | none — `split`+`capitalize`(compose)+`join` | compose (depends on `capitalize` landing first) | same as row above | 3 |
| `removeprefix` | text | none — `starts_with`+`substring` | compose | same | 3 |
| `removesuffix` | text | none — `ends_with`+`substring` | compose | same | 3 |
| `chomp` | text | none — `ends_with("\n")`+`substring` | compose | same | 3 |
| `trim_start_matches` | text | `rt_string_trim_start_matches` (new — repeated-strip loop) | new-logic | `runtime/src/value/text_scan_ext.rs` (new), `codegen/runtime_sffi.rs`, `lowering_expr_method.rs`, `codegen/instr/methods.rs` | 4 |
| `trim_end_matches` | text | `rt_string_trim_end_matches` (new) | new-logic | same as row above | 4 |
| `squeeze` | text | `rt_string_squeeze` (new — char scan) | new-logic | same | 4 |
| `reversed` | text | none — `join(reversed(chars(s)), "")` mirrors the already-landed `sorted` pattern | compose, high confidence | same | 4 |
| `find_all` | text | none — lowering-level loop over repeated `find`/`index_of` | compose via MIR loop (more complex control flow than a one-liner) | same | 4 |
| `replace_first` | text | none — `find`+substring splice | compose | same | 4 |
| `pad_start` | text | none — pad-string via `chars`+`array_repeat`+`join`, then `concat` | compose (depends on the `repeat` composition pattern) | `runtime/src/value/text_pad_ext.rs` (new only if `repeat` needs a helper), `codegen/runtime_sffi.rs`, `lowering_expr_method.rs`, `codegen/instr/methods.rs` | 5 |
| `pad_end` | text | none — same pattern, opposite side | compose | same | 5 |
| `center` | text | none — same pattern, split both sides | compose | same | 5 |
| `zfill` | text | none — `pad_start` with `'0'` | compose (depends on `pad_start`) | same | 5 |
| `repeat` | text | none — `chars(s)`+`rt_array_repeat`(exists)+`join("")` | compose | same | 5 |
| `push_str` | text | **BLOCKED** — shares the reaudit's #3 priority root-cause (`text.push`/`clear`/`reverse` already silent no-ops under JIT) | not applicable until that root-cause lands | (defer; do not implement as a fresh NEEDS-RUNTIME item) | 5 (deferred) |
| `is_numeric` | text | none — `chars`+`char_code_at`+ASCII-range compare+`rt_array_all_truthy` (exists) | compose (ASCII-only; full Unicode would need new Rust) | `lowering_expr_method.rs`, `codegen/instr/methods.rs`, `codegen/runtime_sffi.rs` (for `rt_array_all_truthy` entry) | 6 |
| `is_alpha` | text | same pattern | compose (ASCII-only) | same | 6 |
| `is_digit` | text | same pattern | compose (ASCII-only) | same | 6 |
| `is_alphanumeric` | text | same pattern | compose (ASCII-only) | same | 6 |
| `is_whitespace` | text | same pattern | compose (ASCII-only) | same | 6 |
| `partition` | text | none — `find`+substring split into 3 | compose | same | 6 |
| `rpartition` | text | none — `rfind`+substring split into 3 | compose | same | 6 |

**Totals: 39 methods across 6 batches (Batch 5 nominally 6 + 1 deferred
`push_str`) + a dependency note for `array.remove`/`text.reverse` (not new
batch members, see reconciliation above). Compose-from-existing: 27 of 39.
New-logic (genuinely new Rust): 8 (`ndim`, `chunk`, `transpose`, `dig`
if-variadic, `swapcase`, `trim_start_matches`, `trim_end_matches`,
`squeeze`). Blocked-pending-other-fix: 1 (`push_str`). `compact`(array)/
`fetch`(array) are borderline — likely reclassifiable out of NEEDS-RUNTIME
entirely once someone spot-checks the predicate-callback and default-arg
composition at the lowering level.**

### Recommended execution order

1. Land Part A's Enum fix first (isolated, small, unblocks the Object/Enum
   print bonus row without touching any Part B file).
2. Batches 2, 3, 4, 6 (dict + 3 of the 4 text batches) can start in parallel
   immediately — none contain a genuinely new hard algorithm, all are
   compose-heavy.
3. Batch 1 (array, 3 of 6 new-logic) and Batch 5 (text padding, gated by the
   `repeat`→pad chain, plus the deferred `push_str`) go next; Batch 5's
   `push_str` should be pulled out and handed to whoever fixes the reaudit's
   #3 priority item instead of implemented standalone.
4. Part A Option A (Object out-of-band class registration) can run fully in
   parallel with all of Part B's runtime-code work (new files only); its
   dispatch-arm edit to `closures_structs.rs` should land before or after —
   not during — any Part B batch that also touches that file (none currently
   do, per the batch table, so no live conflict today, but re-check before
   landing if Part B's scope grows).

### Maximum safe parallelism — the honest number

At the **new-runtime-code layer**, all 6 batches are mutually file-disjoint
(each owns its own new `runtime/src/value/*_ext.rs` file, or no new file at
all for pure-compose batches) — **6-way parallel** is safe for writing the
Rust/composition logic itself.

At the **dispatch-arm layer**, every batch's lowering fix lands in the same
shared file, `mir/lower/lowering_expr_method.rs`, and every batch's codegen
arm lands in one of only two shared files,
`codegen/instr/collections.rs` (Batches 1-2) or `codegen/instr/methods.rs`
(Batches 3-6) — **zero batches are mutually file-disjoint** at this layer.
In practice this is low-risk because each batch's edit is a small, additive,
non-overlapping `match` arm (new method-name cases appended, not editing
existing arms) rather than a structural rewrite, so serializing just the
final dispatch-arm merge (not the whole implementation) is the practical
answer: **implement all 6 batches in parallel, land/rebase the two shared
dispatch files' arms one batch at a time** (fast, since each arm is a
self-contained few-line block). If a strict same-file rule is required with
no exceptions, the max safe parallelism is **1** for the dispatch-arm step
and **6** for everything upstream of it.
