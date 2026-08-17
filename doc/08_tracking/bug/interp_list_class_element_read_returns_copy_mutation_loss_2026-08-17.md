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
