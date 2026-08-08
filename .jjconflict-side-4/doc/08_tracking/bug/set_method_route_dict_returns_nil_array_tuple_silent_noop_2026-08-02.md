# `set` method: dict returns nil on the JIT; array/tuple silently no-op when a dict `.set` shares the module

Date: 2026-08-02
Status: OPEN — measured end to end, codegen route NOT located; two hypotheses refuted
Related: `0e711be648d` (the text-mutator lane that measured this), the
`rev`/`reverse` split in `06eb4fe3f8f`

## Why this exists

The mutating-method family sweep recorded that `set` routes to `rt_dict_set` /
`rt_index_set` / `rt_tuple_set` but was **never measured across engines** —
honestly logged as "untested, not assumed correct". This is that measurement.

Binary: the Rust seed built at origin `974a2118ef21` (`cargo build -p
simple-driver`), JIT = default, interpreter = `SIMPLE_EXECUTION_MODE=interpret`.
Every row below is a real run, not a reading of the dispatch tables.

## Measured: one `.set()` per module (isolated)

| receiver | JIT | interpreter |
|---|---|---|
| `var d = {"a": 1}; d.set("b", 2)` | dict mutated (`b == 2`); expression is **`nil`** | dict mutated; expression is **`{a: 1, b: 2}`** |
| `var ar = [10,20,30]; ar.set(1, 99)` | LOUD: `Runtime error: Function 'Array.set' not found` | LOUD: ``error: semantic: method `set` not found on type `array` `` |
| `var tp = (1,2,3); tp.set(0, 77)` | LOUD: `Runtime error: Function 'Tuple.set' not found` | LOUD: ``error: semantic: method `set` not found on type `tuple` `` |

Array and tuple therefore AGREE: both engines refuse. `a[i] = v` index
assignment is the spelling that works, and it was verified to work on both
engines in the same probe (`idx_assign_arr1=99`).

## Defect 1 — `dict.set` expression value diverges (nil vs the dict)

Hand-computed expectation: the mutated dict. Two independent grounds, both
measured, neither of them cross-engine agreement:

- the interpreter (the spec, per the runtime's own `rt_sort` / `rt_reverse_mut`
  doc comments) evaluates `d.set("b", 2)` to `{a: 1, b: 2}`;
- the array mutator precedent agrees — `a.push(4)` evaluates to the mutated
  array `[1,2,3,4]` on **both** engines.

So the JIT's `nil` is wrong. The mutation itself lands correctly, which is why
this has stayed invisible: only code that *uses* the result sees it.

`d.insert(k, v)` (the documented synonym) is identical: `ret2=nil` on the JIT,
`{a: 1, b: 2, c: 3}` on the interpreter.

Not a rendering artefact: the same program printing the dict directly gives
`direct={a: 1}` on the JIT, so the JIT renders dicts fine — the call result
really is nil.

### Refuted hypotheses (both by direct edit, not by reading)

1. **`codegen/instr/methods.rs` `("Dict", "set") | ("dict", "set")`.** Changing
   that arm to yield `receiver_val` instead of `rt_dict_set`'s `bool` changed
   NOTHING: `ret=nil` before and after, on a rebuilt binary.
2. **`codegen/instr/closures_structs.rs` `"set"`.** Same result. Adding a
   `eprintln!` to a new receiver-dispatched `rt_set` and routing that arm to it
   printed the marker **zero** times for a dict receiver, an array receiver, or
   the multi-receiver module.

So the route that actually serves `d.set(k, v)` is neither of the two arms that
`grep '"set"'` finds in the Cranelift lane. It needs to be found before this is
fixed; guessing produced two dead edits already. A fix candidate was written and
then REVERTED rather than landed, because an unreachable helper is unused code
and an unverified edit.

## Defect 2 — array/tuple `.set` goes SILENT when a dict `.set` shares the module

Same three receivers, but all three `.set()` calls in ONE module
(`probe/setroute.spl` shape):

```
var d  = {"a": 1, "b": 2};  d.set("c", 3)
var ar = [10, 20, 30];      ar.set(1, 99)
var tp = (1, 2, 3);         tp.set(0, 77)
```

JIT result:

```
dict_ret=nil   dict_c=3 dict_a=1        <- dict still works
arr_ret=0      arr1=20  arr0=10         <- SILENT: no mutation, no error
tup_ret=0      tup0=1   tup2=3          <- SILENT: no mutation, no error
```

The interpreter still refuses the array loudly in exactly this module. So an
UNRELATED dict `.set()` elsewhere in the same module converts a loud failure
into a silent wrong answer — the array is not modified, and `0` is handed back
as though it were an answer. This is the erased-receiver name-binding class
already catalogued in
`codegen_bare_method_receiver_type_blind_candidate_selection_2026-07-28.md`:
the type-blind `set` arm calls `rt_dict_set` on whatever receiver reaches it,
and `rt_dict_set` on an array returns `false`, rendered `0`.

Confirmed attributable to that arm: repointing it away from `rt_dict_set`
flipped both rows from the silent `0` back to the loud
`Function 'Array.set' not found` / `Function 'Tuple.set' not found`, matching
the interpreter. That change was NOT landed, because the same repoint would
also strand any genuinely erased DICT `.set` — the replacement helper never
resolved through `ctx.runtime_funcs`, so the arm falls through for every
receiver, and no erased-dict `.set` case was found to prove that safe.

## What a fix has to do

1. Find the real `Dict.set` lowering (not `instr/methods.rs`, not
   `instr/closures_structs.rs`) and make it yield the receiver.
2. Make the type-blind `set` arm receiver-dispatched instead of
   unconditionally `rt_dict_set`, in the shape `rt_at` / `rt_find` / `rt_sort` /
   `rt_reverse_mut` already use — with an erased-dict `.set` fixture proving the
   dict path still resolves, and an array/tuple fixture proving the refusal
   stays loud.
3. Keep `a[i] = v` (`rt_index_set`) untouched; it is a different route and it
   works on both engines.

## Not in scope here, but on the record

`codegen/llvm/**` has **no `rev` / `reversed` arm at all** — all four of its
method tables map only `"reverse" => rt_reverse_mut`, while the Cranelift lane
has `"rev" | "reversed" => "rt_reverse"`. `syntax_quick_reference.md` documents
`.reversed()` as the spelling for reversing "a list, string, or tuple", so the
arm SHOULD exist. It was deliberately not added: the native lane could not be
built in this lane's scratch clone (`error: LLVM native linking failed: Runtime
compilation failed: Runtime source directory not found. Expected
src/runtime/runtime.c`), and an unmeasured dispatch-table edit is exactly what
the `reverse`/`sort` pins in
`codegen/instr/closures_structs.rs` exist to prevent.
