# Bare-method codegen binds by name-suffix with no receiver-type check

**Date:** 2026-07-28
**Severity:** high — silent wrong-code generation; victims are currently
discovered by guest page faults, one at a time
**Status:** OPEN (mitigated per-name only)
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
victims are found by crashes.** `equals` is the obvious next one — 19 `fn equals`
definitions exist in owned source.

## Suggested next steps, cheapest first

1. **Make the single-candidate erased-receiver bind observable.** Emit a
   level-gated (default-off) diagnostic naming the receiver vreg, method, and
   bound symbol. Zero behavior change, zero regression risk, and it converts
   discovery from "guest page fault" to "compile-time message". Run it over the
   bootstrap closure to size the class before attempting 2 or 3.
2. Add the arity filter behind that measurement, once the placeholder-signature
   question in (2) above is settled.
3. Plumb a TypeId-to-name map into `InstrContext` and check the receiver type.
   This is the actual root fix.

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
