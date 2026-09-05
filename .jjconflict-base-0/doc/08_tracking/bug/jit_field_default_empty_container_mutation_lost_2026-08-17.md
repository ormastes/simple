# JIT: declared field defaults dropped at construction — ALREADY FIXED in-tree, live in the deployed seed

- **Status:** RESOLVED in current source, verified by execution 2026-08-17.
  **Still wrong in the deployed `bin/simple`** (mtime 2026-08-16 22:59), which
  predates the fix. Anything measured against that binary reproduces it.
- **Severity as it was:** P1, silently-wrong-result — compiled clean, exited 0,
  handed back wrong values.
- **Engines:** JIT only (the DEFAULT engine). The interpreter was always correct.
- **Collapses these filed rows into one cause:**
  - `struct_field_array_pop_no_shrink_2026-07-30.md` — the `.pop()` symptom is
    downstream; the `.push()` that filled the array never landed either, and the
    filed root cause (`interpreter_method/mod.rs`) is wrong on both counts: the
    interpreter is the CORRECT engine here, and `.pop()` is not the failing op.
  - the "container mutation silently discarded" shape generally, when observed
    on a `[]`/`{}`-defaulted field.
- **Fixed by:** the `declared_default` arm of `lower_struct_init_fields`,
  `src/compiler_rust/compiler/src/hir/lower/expr/collections.rs:~452`
  ("ROOT FIX (JIT omitted-field-default), 2026-08-17"), reached from both
  construction shapes — brace literal (`collections.rs`) and paren call
  (`hir/lower/expr/calls.rs:98`). Classified by CONTENT and confirmed by running
  a build of the tree, not by SHA ancestry.

## What the defect was

Under the JIT, **every declared field default was dropped at construction and
every unwritten slot got the raw nil tag**. `i64` surfaced as `3` (the tag
itself), `f64` as `0`, `str` as a len `-1` string, a nested struct as `0`, and a
container as a degenerate handle that *accepted* a mutation and then discarded
it. Only `bool` survived, because the nil tag is truthy.

That last one is what made it so damaging: the canonical accumulator idiom

```
class Doc:
    var lines: [str] = []
    fn add(mut self, s: str):
        self.lines.push(s)
```

returned an empty list, with rc 0 and no diagnostic.

## Evidence — before and after, same probes, same machine

Probes (committed, both engines, all oracles are absolute literals the probe did
not itself compute):

- `test/01_unit/compiler/codegen/probe_declared_default_object_identity_jit.spl` (18 checks)
- `test/01_unit/compiler/codegen/probe_field_default_container_jit.spl` (9 checks)

**BEFORE — deployed `bin/simple`, `SIMPLE_EXECUTION_MODE=jit`, rc=0:**

```
FAIL default_i64_reads_7 got=3 want=7          <-- the raw nil tag 3
FAIL default_f64_reads_1_5 got=0 want=3
FAIL default_str_len_1 got=-1 want=1
FAIL default_array_accepts_push got=0 want=1
FAIL default_array_second_push got=0 want=2
FAIL default_array_pop_shrinks got=0 want=1
FAIL default_str_array_accepts_push got=0 want=1
FAIL default_dict_accepts_insert got=-1 want=1
FAIL default_nested_struct_field got=0 want=11
FAIL class_default_i64 got=3 want=7
FAIL class_default_array_push got=0 want=1
FAIL class_default_dict_insert got=-1 want=1
DECLARED_DEFAULT_OBJECT_IDENTITY PROBE: 12 FAILURES

FIELD_DEFAULT_CONTAINER PROBE: 5 FAILURES
```

Interpreter arm on the same binary: both probes ALL PASS.

**AFTER — seed built from the current tree**
(`CARGO_TARGET_DIR=/mnt/data/cargo-target-rustinterp cargo build --release --bin simple`,
`Finished release profile in 9m 27s`):

```
== interpreter  DECLARED_DEFAULT_OBJECT_IDENTITY PROBE: ALL PASS
== jit          DECLARED_DEFAULT_OBJECT_IDENTITY PROBE: ALL PASS
== interpreter  FIELD_DEFAULT_CONTAINER PROBE: ALL PASS
== jit          FIELD_DEFAULT_CONTAINER PROBE: ALL PASS
```

## Isolation recorded for the next reader

Four-way probe on `struct S: var n: i64 = 3; var arr: [str] = []`, on the
deployed seed:

| case | source | interp | jit |
|---|---|---|---|
| A | read `s.arr.len()` on the default | 0 | 0 |
| B | `s.arr.push("z")` on the default | 1 | **0 WRONG** |
| C | `s2.arr = fresh_empty_local; s2.arr.push("z")` | 1 | 1 |
| D | `s3.arr = ["a"]; s3.arr.push("z")` | 2 | 2 |

C is what named the cause: assigning *any* freshly-constructed container — even
an empty one — first made the mutation stick, so the defect was in the object the
construction site materialized, not in mutation or field write-back. Explicit
read-modify-writeback (`tmp = d.lines; tmp.push(..); d.lines = tmp`) still gave 0,
which rules out the COW write-back family (`merge_shared_collection_fields`,
`interpreter_call/core/function_exec.rs:975-1015`) — that is interpreter-only, and
the interpreter was the engine that was right.

## Two traps this cost, worth carrying forward

1. **Do not probe this area with the default values `0`, `1` or `3`.** An early
   probe on `var n: i64 = 3` read back `3` and was scored "correct". It was the
   nil tag coinciding with the declared default. The bug was invisible until a
   default of `7` was used.
2. **The deployed seed is not the tree.** Every failure above is real on the
   binary that ships and completely absent from a build of current HEAD. Reading
   the `collections.rs` fix comment and calling it fixed would have been right;
   trusting the deployed binary would have produced a second patch for a
   defect that no longer exists. Only rebuilding settles it.

## Regression guards added

- `test/01_unit/compiler/codegen/field_default_container_mutation_spec.spl`
  — reproducing spec (RED on the deployed seed, GREEN on current tree).
- `test/01_unit/compiler/codegen/declared_default_object_identity_class_spec.spl`
  — class-detection spec: sweeps bool/i64/f64/str/array/str-array/dict/nested-struct
  defaults on both a struct and a class, with a differential control arm
  (explicitly assigned empty container) so a future regression that is *broader*
  than construction-site defaults is distinguished from this one.

Both shell out to a subprocess under both engines: a spec body runs on the
INTERPRETER, which was correct throughout, so an in-process example can never go
red on this defect.
