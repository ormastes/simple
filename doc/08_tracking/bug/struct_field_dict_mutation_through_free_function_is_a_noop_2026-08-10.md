# struct field dict mutation through a free function is a silent no-op

## RESOLUTION 2026-08-17 — resolution (B) shallow, implemented in the interpreter

Unblock condition 2 ("the write is propagated back to the caller"), scoped to
the field kinds that are genuinely shared handles.

**Engines.** Interpreter ONLY. JIT and native/AOT already made the write
visible; the interpreter was the outlier, which is what made the divergence
invisible to positive assertions. Re-measured on the deployed pre-fix binary
with an absence control in every run:

```
== interpreter                     == jit
struct has answer=false            struct has answer=true
struct has never=false             struct has never=false
class  has answer=true             class  has answer=true
```

**Root cause (exact).** Interpreter dicts/arrays are `Value::Dict(Arc<HashMap>)`
with copy-on-write, so a callee mutation `Arc::make_mut`s a fork that dies with
the frame. Visibility depends entirely on the post-call env write-back in
`write_back_mutable_arguments`
(`src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs:969`),
and `is_value_type_struct` (`:953`) excluded EVERY value-type struct from it
outright — correct for scalars, wrong for container handles. The
`self.values[k] = v` code itself is identical for `class` and `struct`
(`interpreter/node_exec.rs:1429-1487`); only the write-back gate differed.

**Fix.** `merge_shared_collection_fields` carries back ONLY `Array`/`Dict`/
`ByteArray`-valued fields of a value-type struct. Scalar and nested-struct
fields keep strict value semantics, so "struct is a value type" still holds and
task #91 is not regressed — deliberately NOT a whole-struct write-back.

**Specs:**
- reproducing: `test/01_unit/compiler/interpreter/struct_container_field_mutation_spec.spl`
  (in-process examples + a subprocess interpreter-vs-JIT cross-check)
- similar-problem detection: `test/01_unit/compiler/interpreter/value_type_field_mutation_class_spec.spl`
  (array fields, second-hop and method mutation routes, nested depth, and the
  scalar-stays-invisible control that fails on an over-corrected fix)

Reproduce-first evidence, deployed pre-fix binary: `3 examples, 2 failures` and
`5 examples, 3 failures` respectively.

**The fix is SEED-SIDE and is only provable after a seed rebuild/redeploy.**

- **Status:** FIXED in the seed interpreter (pending redeploy)
- Original report follows.

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
