# Reading a class element out of a `[Class]` field returns a COPY; `me`-method mutation is lost

- **Status:** OPEN
- **Filed:** 2026-08-17
- **Severity:** HIGH (silent wrong answer, no diagnostic)
- **Engine:** tree-walk interpreter (`bin/simple test`, and `bin/simple run` with
  `SIMPLE_EXECUTION_MODE=interpreter`)
- **Binary observed:** `bin/release/x86_64-unknown-linux-gnu/simple`,
  59621024 bytes, 2026-08-17 20:28:24 UTC

## Minimal repro (5 lines of logic)

```simple
class Item:
    n: i64

impl Item:
    me bump():
        me.n = me.n + 1

class Box:
    items: [Item]

impl Box:
    me first() -> Item:
        me.items[0]

fn main():
    val b = Box(items: [Item(n: 0)])
    val it = b.first()
    it.bump()
    print("local={it.n} refetch={b.first().n} direct={b.items[0].n}")
```

Observed: `local=1 refetch=0 direct=0`
Expected: `local=1 refetch=1 direct=1` — `Item` is a **class**, so element reads
must alias, not snapshot.

The mutation is visible only through the local binding. The owning list never
sees it, and nothing warns.

## How it was found

`test/01_unit/app/office/cursor_hidden_row_invariant_spec.spl` went
`6 total, 6 passed` -> `6 total, 0 passed, 6 failed`. The initial hypothesis was
a compiler regression breaking all three cursor paths at once. **That hypothesis
is disproved.** Instrumenting `_all_paths` shows:

```
PATHS g=2 t=2 a=1      # down, single hidden row  (expected 2)
PATHS g=4 t=4 a=1      # down over a run          (expected 4)
PATHS g=0 t=0 a=1      # up                       (expected 0)
```

GUI and TUI are correct. Only the `SheetsApp` path is wrong, and the failure
texts (`expected 1 to equal 2` etc.) are the `rows[2] == rows[0]` assertions,
not `rows[0]`.

Mechanism, confirmed by a direct probe:

```
P2 local_sh len=1 hid2=true      # after sh.hide_row(2)
P2 refetched len=0 hid2=false    # app.workbook.active() again
```

`Workbook.active()` (`src/app/office/sheets/spreadsheet.spl:245-247`) returns
`me.sheets[me.active_sheet]`. The spec fixture (`_app_row_after`) does
`val sh = app.workbook.active()` then `sh.hide_row(r)`; the hide lands on a
detached copy. `SheetsApp.navigate_to`
(`src/app/office/sheets/sheets_app.spl:192`) then re-reads `me.workbook.active()`
— a sheet with **no** hidden rows — so its skip loop is a correct loop over an
empty predicate and the cursor lands on row 1.

`Sheet.is_row_hidden`, `Sheet.hide_row`, and all three skip loops are verified
correct in isolation (`hid2=true`, GUI/TUI land right).

## Shared root cause with the sibling records (verified by source, 2026-08-17)

This record is the **canonical carrier of the root cause** for the
class-value-identity family. The mechanism, verified directly in this tree by
grep (not inherited from another agent's report):

- `Value::ClassInstance(Arc<ClassInstance>)` exists — `ClassInstance` is
  declared at `src/compiler_rust/compiler/src/value.rs:1114` with its `impl`
  block at `:1119`, and the variant is carried through `value_impl.rs`,
  `value_bridge.rs`, `value_pointers.rs` and ~16 sites in
  `interpreter/node_exec.rs`.
- **It has ZERO producers.** `grep -rn "ClassInstance::new"` over
  `src/compiler_rust` returns 0 hits; `grep -rn "ClassInstance::"` returns only
  vendored Win32 `ID3D11ClassInstance` noise; there is no
  `Arc::new(ClassInstance` and no `ClassInstance { .. }` struct literal outside
  `value.rs` itself. Every `Value::ClassInstance` site in the interpreter is a
  **consumer or a re-wrap of an already-existing instance** — nothing ever
  constructs one. The variant is unreachable code.
- Consequence: source-level `class` values are represented as `Value::Object`,
  the copy-on-write STRUCT carrier (`Object { class: String, fields:
  Arc<HashMap<..>> }`, `value.rs:1114` region). There is no class-vs-struct
  discrimination in `src/compiler_rust/compiler/src/interpreter/`. Class
  identity is *simulated* by path-based write-back at assignment/call
  boundaries, which is exactly why in-place chained mutation
  (`box.items[0].bump()`) works while bind-then-mutate silently loses the write.

**Designed-but-unwired mechanism — second instance of a pattern.** A complete
value variant landed with full consumer plumbing and zero producers. The other
known instance in this codebase is `interface_digest_of`
(`src/compiler/80.driver/.../action_key.spl`), documented in
`.claude/rules/commands.md` as having exactly one grep hit — its own definition.
Recorded as a **pattern worth watching for** (a designed mechanism can be merged,
reviewed and documented while being wired to nothing, and every consumer-side
grep will make it look live). No claim is made that the two are otherwise
related.

**Blast radius (reported by another agent, NOT verified here):** 274
index-bind-then-mutate sites across 87 files, 66 of them without a compensating
write-back. Treat as an unconfirmed estimate until re-counted.

## Family status — the sibling records are CLOSED, so this is NOT a three-way merge

The two sibling records below share this root cause but are **not** currently
reproducing. They were deliberately left as independent records rather than
folded in: each documents a separate discovery at a separate access site, and
three independent discoveries are themselves evidence of severity.

| record | access site | status |
|---|---|---|
| this one (2026-08-17) | list element read out of a `[Class]` field | **OPEN**, live RED spec |
| `interpreter_binding_class_typed_field_snapshots_instead_of_aliasing_2026-08-10.md` | class-typed **field** bind | CLOSED — did-not-reproduce 2026-08-17 |
| `interp_dict_class_value_copy_on_get_mutation_loss_2026-07-06.md` | `Dict.get()` | CLOSED — NOT REPRODUCED, two independent EXECUTION re-measurements 2026-08-17 |

That split is consistent with the root cause rather than contrary to it: the
path-based write-back simulation has been extended to cover the dict-get and
field-bind sites, but not the list-element-read site. The engine defect (no real
reference values) is unfixed; only two of its three surfaces are papered over.

**Correction to the 2026-08-10 record.** Its closing triage section attributes
the fix to "the `ClassInstance(Arc<ClassInstance>)` shared-identity value variant
added in `a155bff913f4`". That attribution is **wrong**: per the zero-producer
grep above, the variant is never constructed and therefore cannot be giving any
value reference semantics. Its did-not-reproduce *observation* may still be
sound — it rests on an execution run — but its stated *mechanism* is not.

## Fix options

- **A — construct `Value::ClassInstance` at class-constructor lowering and plumb
  it through** field access, method dispatch, pattern matching, equality,
  printing and FFI/bridging. This is the real fix: it gives `class` genuine
  reference semantics and closes all three surfaces at once, including the ones
  currently masked by write-back. Cost is a value-model change; the 2026-08-10
  record notes ~210 non-vendor `Value::Object` match sites (reported there, not
  re-counted here) and an existing test,
  `interpreter/node_exec.rs::field_assignment_cow_protects_struct_local_alias`,
  that locks the current COW behaviour and must be updated to register its
  `Point` as a value type.
- **B — narrow aliasing of `Expr::Index` only. REJECTED as unsound.** You cannot
  alias without a shared cell; with `fields: Arc<HashMap<..>>` and
  `Arc::make_mut`, any "alias" is a clone the moment it is written through. A
  targeted `Expr::Index` change can only re-add another path-based write-back,
  i.e. more of the simulation that already fails on the next unhandled shape.
- **C — local workarounds** (`wb.sheets[i] = sh`, `caches.set(id, cache)`).
  Papers over the engine defect. Already in tree at the office and
  host-compositor call sites; not a fix, and not a reason to close this record.

## Not the same as existing records

- `interp_dict_class_value_copy_on_get_mutation_loss_2026-07-06.md` — Dict
  `.get()`, not list element read.
- `interpreter_binding_class_typed_field_snapshots_instead_of_aliasing_2026-08-10.md`
  — a class-typed *field* binding, not an element of a `[Class]` field.
- `aliased_array_mut_param_mutation_lost_interpreter_2026-08-06.md` — param
  aliasing, not element read.

Likely the same root cause family; kept separate because the trigger shape and
the repro differ.

## Unblock condition

The minimal repro above must print `local=1 refetch=1 direct=1` under
`SIMPLE_EXECUTION_MODE=interpreter`. Then
`bin/simple test test/01_unit/app/office/cursor_hidden_row_invariant_spec.spl`
must return to `6 total, 6 passed, 0 failed`.

**Do not weaken the spec.** It is asserting a real invariant and is correctly
RED. A defensible interim workaround in office code only would be to have
`Workbook.active()` callers write the sheet back
(`wb.sheets[i] = sh`), but that papers over the engine defect and is not the fix.
