# Bare-method codegen binds by name-suffix with no receiver-type check

**Date:** 2026-07-28
**Severity:** high — silent wrong-code generation; victims are currently
discovered by guest page faults, one at a time
Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
**Component:** `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs`
(cranelift seed codegen), `compile_method_call_static`

## Symptom

A method call on a receiver whose static type was ERASED reaches codegen as a
bare (dot-less) `MethodCallStatic`. Codegen then binds it to whatever
`Type_dot_<method>` symbol happens to be linked into the entry closure, reading
the receiver as that unrelated struct and dereferencing garbage.

Known victims, each found by a crash and each patched individually:

| method | victim binding | found |
|---|---|---|
| `get` / `has` / `contains` / `remove` / `find` | `SymbolTable.get`, `SuffixRegistry.has`, `StaticCompressionCache.get` | 2026-06-10..17 |
| `len` / `length` | `ListIter.len` | 2026-06-11 |
| `starts_with` / `ends_with` | `ByteSpan.starts_with` (page-faulted the SimpleOS WM guest) | 2026-07-27 |
| `slice` | `ByteSpan.slice` / same-module `Foo.slice` | 2026-07-28 |

## Measured evidence (2026-07-28)

Fixture: a same-module `struct Foo` carrying
`slice / starts_with / equals / find / get / index_of`, erased receivers via
`.lower()` / `.upper()` / `.substring(1)`, and a `.trim()` control.
Reloc census via `objdump -r` on `mod_0.o`, cranelift backend,
`--target x86_64-unknown-none --entry-closure`.

| symbol | seed `eebfb3a7` (no `slice` entry) | seed `c81588d1` (with entry) |
|---|---|---|
| `rt_slice` | 2 | 6 |
| `Foo_dot_slice` | **5** | 1 |
| `Foo_dot_{starts_with,equals,find,get,index_of}` | 1 each | 1 each |

Only ONE of those five `Foo_dot_slice` relocs is a genuinely typed
`f.slice(1, 3)`. The other four were erased-receiver text calls, stolen.

## Enumeration of the class (2026-07-28, `SIMPLE_DEBUG_ERASED_RECEIVER_BIND`)

Step 1 below is now implemented. `SIMPLE_DEBUG_ERASED_RECEIVER_BIND=1` reports
every erased-receiver name-suffix bind (calling function, bare method + arity,
receiver `TypeId`, bound symbol). It is report-only — proven by byte-identical
archives from patched and unpatched seeds built in one isolated
`CARGO_TARGET_DIR` (`mod_0.o` sha256 `ddeeda0818b74440…`, archive
`f020994b7d37c2f7…`, identical for control / patched-off / patched-ON).

Census over the `gui_entry_desktop` SimpleOS closure (39 imports, whole
`src/os` + `src/lib` transitive graph, cranelift, `x86_64-unknown-none`,
`--entry-closure`): **97 erased-receiver binds, 22 distinct method names, 30
distinct (method, arity, receiver-type, target) tuples.** 45 had
`receiver_ty=ANY`, 34 had no receiver type at all.

| bare method | binds | bound to | reading |
|---|---|---|---|
| `to_i64` | 33 | `failsafe.core.LogLevel.to_i64` | THEFT — scalar/text builtin |
| `unwrap` | 21 | `failsafe.core.FailSafeResult.unwrap` | THEFT — Option/Result builtin |
| `to_i32` | 8 | `window_protocol.geometry.Px.to_i32` | THEFT — scalar builtin |
| `index_of` | 8 | `dbfs_engine.txn.TxnStepSequence.index_of` | THEFT — text/array builtin |
| `to_u32` | 2 | `fb_driver.Color.to_u32` | THEFT — scalar builtin |
| `to_text` | 2 | `PackageVersion.to_text`, `ReadbackSource.to_text` | THEFT — universal builtin |
| `push` | 1 | `bytes.window.RingWindow.push` | THEFT — array builtin |
| `rollback` | 3 | `database.sql.transaction.Transaction.rollback` | probably legit erased-field dispatch |
| `get_pixel_buffer` / `set_pixel_buffer_override` | 5 | `Engine2dCompositorBackend.*` | legit erased-field dispatch |
| `clear` / `draw_image` / `read_pixels_with_source` / `shutdown` | 6 | `gpu.engine2d.Engine2D.*` | legit erased-field dispatch |
| `as_text` / `as_int` / `as_real` / `as_bool` | 4 | `DbValue.*` | legit erased-field dispatch |
| `diagnostic_text`, `ftruncate`, `has_swapped_mapping`, `init_bounce_buffer` | 4 | assorted | legit erased-field dispatch |

Widening to three SimpleOS closures (`gui_entry_desktop` 97, `desktop_e2e_entry`
68, `os_entry` 45) gives **210 binds over 22 distinct method names and 36
distinct tuples**, i.e. each additional closure keeps adding new tuples rather
than converging.

`equals` did not appear in this closure, but the fixture confirms it is
stealable: an erased `text` receiver bound `equals` and `index_of` to
`Foo.equals` / `Foo.index_of` (matching `Foo_dot_equals` / `Foo_dot_index_of`
relocs of 1 each).

**Conclusion: the set is neither small nor closed.** One closure alone adds
seven previously-unknown builtin-idiom victims (`to_i64`, `to_i32`, `to_u32`,
`to_text`, `index_of`, `unwrap`, `push`) on top of the four already patched, and
roughly a fifth of the binds are *legitimate* erased-field dispatch that an
allowlist must not break. Completing `is_bare_builtin_collection_method` is
therefore not a route to closing the class — it would keep growing per closure,
and each entry risks the legitimate dispatches. **Step 3 (plumb a
TypeId-to-name map into `InstrContext` and check the receiver type) is the fix.**
Step 2 (arity filter) remains the useful interim narrowing: many of the thefts
above are 0-arg calls landing on 0-arg methods, so arity alone would not have
caught them either.

## Root cause, and a correction to the earlier reading

The earlier write-up blamed the "pick shortest name" fallback. That is **not**
the live path. The `candidates.len() > 1` case already emits a loud
`[CODEGEN-AMBIGUOUS-METHOD]` diagnostic and returns `None` (added 2026-04-13),
so `min_by_key` is only ever reached with `candidates.len() <= 1`.

**The control build that stole four calls emitted ZERO diagnostics.** The wrong
pick therefore went through the **single-candidate** path: exactly one
`Type_dot_slice` was linked in, so there was no ambiguity to report, and the
name-suffix match alone bound it.

This matters because it means *narrowing among candidates cannot close the
class*. The defect is that selection never consults the receiver type at all.

## Correction (2026-08-01): Step 3 alone cannot decide the ANY cases

Measured under the Rust seed's cranelift JIT with
`SIMPLE_DEBUG_ERASED_RECEIVER_BIND=1`, one construct per file:

| fixture | receiver | reported `receiver_ty` | bound to | verdict |
|---|---|---|---|---|
| `"hello world".lower().index_of("world")` with a same-module `Str.index_of` | erased text | `Some(TypeId(14))` = `TypeId::ANY` | `Str.index_of` | **THEFT** (999, not 6) |
| `self.backend.shutdown()` where `backend: any` holds a `Backend` | erased field | `Some(TypeId(14))` = `TypeId::ANY` | `Backend.shutdown` | **LEGIT** (42) |

Both report the *same* `receiver_ty`. A TypeId-to-name map therefore cannot
separate theft from legitimate erased-field dispatch for the 79 of 97 census
binds that were `ANY` (45) or untyped (34) — Step 3 can only adjudicate the
remaining 18 with a concrete receiver type. **The only compile-time-available
discriminator for the ANY majority is the runtime tag**, i.e. a genuine fix has
to emit a tag test and branch between the `rt_*` builtin and the name-bound user
method. No such predicate is exported by the runtime today
(`rt_value_is_heap` does not distinguish a text/array/dict from a user struct).

Also measured, and why the blanket form of Step 3's alternative is unsafe:
"always try the builtin first for a bare name" would hijack `clear`
(`rt_array_clear`) plus `set` / `find` / `sort` / `map` / `filter` / `first` /
`last` / `hash` / `at` / `replace` / `split` / `reverse` — all common user method
names that legitimately reach this path. The builtin table is much wider than
`is_bare_builtin_collection_method`, so it cannot simply replace it.

Separately, the numeric casts (`to_i64` 33 binds, `to_i32` 8, `to_u32` 2) must
NOT be added to `is_bare_builtin_collection_method`: their builtin lowering is a
*static* cast keyed on `vreg_types` (`from_ty`), not a tag dispatch, so on an
`ANY` receiver it would reinterpret a tagged pointer as a number. Routing them
to the builtin trades one wrong answer for another.

## Why it is not a contained fix

1. **No receiver-type check is possible at this layer.** `InstrContext`
   (`codegen/instr/mod.rs:95`) carries `vreg_types: HashMap<VReg, TypeId>`, so
   the receiver's `TypeId` is available — but there is **no TypeId-to-name
   mapping anywhere in codegen** (verified by grep). Candidates are only known
   by mangled *name*. Comparing the two requires plumbing a type-name registry
   (or the HIR type table) into `InstrContext`. That is the real fix and it is
   a cross-layer change.
2. **An arity check helps but does not close it.** Candidate signatures are
   reachable via `ctx.module.declarations().get_function_decl(id).signature`.
   In the fixture this would have caught the 1-arg `.slice(2)` case
   (`Foo.slice` has 3 sig params vs valid `{1,2}`) but NOT the 2-arg
   `.slice(1, 3)` case (3 params matches valid `{2,3}`). It is a partial
   mitigation with its own hazard: cross-module imports are in places declared
   with a placeholder generic `i64 -> i64` signature
   (see `compile_closure_create`), which an arity filter would wrongly drop.
   Needs full-bootstrap validation before landing.
3. **Refusing all erased-receiver name-suffix binds** would close the class in
   a few lines, generalizing the existing unconditional `has` / `len` /
   `length` guards. But many legitimate dispatches rely on that path (e.g.
   `self.backend.draw_rect_filled(...)` where the field type is unknown at the
   call site). Blast radius is unmeasured and needs a full bootstrap.

## Current mitigation

A per-name allowlist, `is_bare_builtin_collection_method`, routes known-hazardous
bare names to tag-dispatching `rt_*` builtins before name resolution. It is
gated on `!lookup_name.contains('.')`, so genuinely typed receivers still reach
their real methods — confirmed above (typed `Foo_dot_*` relocs unchanged).

This is a denylist-shaped defense: **every new victim needs a new entry, and
victims are found by crashes.** `equals` is *not* in fact reachable this way:
`try_compile_builtin_method_call` has no `equals` arm, so a bare `equals` falls
through regardless of whether it is listed.

2026-08-01: `("index_of", 1)` added, this time found by a minimal repro rather
than a crash. `rt_index_of` tag-dispatches (`rt_array_index_of` fails closed with
-1 on a non-array, then `rt_string_find`), so it is safe on any receiver.
Regression spec: `test/01_unit/compiler/codegen/erased_receiver_index_of_bind_spec.spl`
(+ its `fixtures/erased_receiver_index_of.spl`). The spec shells out to a `run`
subprocess on purpose — `use std.spec` demotes the whole program to the tree-walk
interpreter, so an in-process `it` block cannot reach this codegen path at all
and passes identically on fixed and unfixed compilers.

## Suggested next steps, cheapest first

1. ~~**Make the single-candidate erased-receiver bind observable.**~~ DONE
   2026-07-28 — `SIMPLE_DEBUG_ERASED_RECEIVER_BIND`, see the enumeration section
   above. Discovery is now a compile-time message, not a guest page fault.
2. Add the arity filter behind that measurement, once the placeholder-signature
   question in (2) above is settled.
3. ~~Plumb a TypeId-to-name map into `InstrContext` and check the receiver
   type.~~ **Superseded 2026-08-01** — see the Correction section: theft and
   legitimate erased-field dispatch both report `receiver_ty = ANY`, so this
   closes at most 18 of the 97 census binds. Worth doing for those 18, but it is
   not the root fix.
4. **New root-fix candidate:** export a runtime predicate that distinguishes a
   builtin value (text / array / dict / scalar) from a user struct, then emit a
   tag test at every erased-receiver name-suffix bind that has a tag-dispatching
   builtin of the same name, branching between the two. This is the only
   discriminator that is actually correct in the `ANY` majority. Cost: one new
   `rt_*` symbol plus block emission in `compile_method_call_static`; needs a
   full bootstrap to validate.

## Repro

Fixture and oracle used for the census are described above; the census command is

    objdump -r mod_0.o | grep -oE '[A-Za-z0-9_]+_dot_(slice|starts_with|equals|find|index_of|get|len)|rt_slice'

against an archive built with
`native-build --entry-closure --emit-archive --target x86_64-unknown-none --backend cranelift`.

## Related

- `8d1d0a4476c` — added `starts_with` / `ends_with` to the allowlist
- `bea738bdb0b` — added `slice` to the allowlist (this investigation)
- In-file `SAFETY NOTE (Agent δ, 2026-04-13)` documents the ambiguity half,
  which is already loud
