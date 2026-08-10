# struct field dict mutation through a free function is a silent no-op

- **Status:** OPEN — spec left RED deliberately
- **SUPERSEDED FRAMING — read first:**
  `struct_dict_field_mutation_engine_divergence_2026-08-10.md`. The "value
  semantics, write discarded" conclusion below was drawn from the INTERPRETER
  only. Measured across all three engines with absence controls: interpreter
  `false`, **JIT `true`, native/AOT `true`**. It is an engine divergence, and
  the intended copy DEPTH for a Dict field inside a struct is UNDOCUMENTED.
- **Filed:** 2026-08-10
- **Spec (both duplicate trees, both execute):**
  - `test/unit/compiler/interpreter/self_field_assign_spec.spl` — `Results: 13 total, 12 passed, 1 failed`
  - `test/01_unit/compiler/interpreter/self_field_assign_spec.spl` — `Results: 7 total, 6 passed, 1 failed`
- **Failing example:** `preserves struct dictionary-field mutations through returning free functions`
- **Reported:** `expected subject to be truthy, got false`

## Symptom

```
fn write_struct_dict_holder(self: MutableStructDictHolder, key: text, next: i32) -> DictWriteResult:
    self.values[key] = next
    DictWriteResult.Success
```

The assignment executes, the function returns `DictWriteResult.Success`, and the
caller's `holder` is **unchanged** — `holder.values.has("answer")` is `false`.

## Controlled A/B (same file, same run, only `class` vs `struct` differs)

| holder declared as | helper | verdict |
|---|---|---|
| `class MutableDictHolder` + `write_dict_holder` | `self.values[key] = next` | **PASS** |
| `struct MutableStructDictHolder` + `write_struct_dict_holder` | `self.values[key] = next` | **FAIL** |

`class` is a reference type, `struct` is a value type, so the helper mutates a
copy of the struct and the write is discarded at the call boundary. The dict
field is not shared through the copy.

## Why it was invisible

The example asserted only `expect(holder.values.has("answer")).to_equal(true)`
and wrapped it in `match result: case DictWriteResult.Success:` — a
single-variant enum, so the `case _:` arm is unreachable and the `match` proves
nothing. The example has now been given the value assertion plus an
**absence control** (`has("never-written") == false`), so a dict that answers
`true` to everything cannot fake a pass either.

## Unblock condition

Either
1. the compiler rejects `self.<field>[k] = v` in a free function whose
   parameter is a value-type `struct` (a diagnostic, not a silent no-op), or
2. the write is propagated back to the caller (out-parameter / explicit
   returned-struct semantics),

and then this example goes green without weakening any assertion.

## Do not

Do not soften this to `.has()`-only, mark it pending, or delete the example.
It documents a real value-type footgun that currently fails silently.
