# `set` method: dict returns nil on the JIT; array/tuple silently no-op when a dict `.set` shares the module

Date: 2026-08-02
Status: ARCHITECTURAL-OPEN — re-verified 2026-08-09 and again fresh
2026-08-10; still architectural/out-of-scope for a .spl/.shs-only lane.
Superseded characterization (more precise root cause, self-hosted lane):
`dict_set_bracket_write_parity_2026-08-07.md`.

### Re-verification 2026-08-10

Re-ran Defect 1's minimal repro against the currently deployed seed
(`bin/release/x86_64-unknown-linux-gnu/simple`):

```
var d = {"a": 1}
val ret = d.set("b", 2)
print "ret={ret}"; print "b={d[\"b\"]}"
```

- default JIT: `ret=nil`, `b=2` — matches doc exactly (mutation lands, return
  value is wrong).
- `SIMPLE_EXECUTION_MODE=interpreter`: `ret={a: 1, b: 2}`, `b=2` — correct,
  matches doc exactly.

Confirms Defect 1 is unchanged. Root cause remains in the Rust seed's
Cranelift codegen (`src/compiler_rust/**`, off-limits to this and any
.spl-only lane), and the self-hosted-lane companion defect (`.set`/`.insert`
missing from `is_dict_method_name` in
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`) sits in a
file this task's own hard constraints explicitly forbid editing (owned by a
concurrent session). No further action possible from this lane; leaving
OPEN/ARCHITECTURAL as previously assessed.

## Re-verification 2026-08-09

Re-read fresh. The root cause found by the later 2026-08-07 investigation is
sharper than this file's own "codegen route NOT located": on the **self-hosted
lane**, `d.set(k, v)` fails MIR lowering outright with
`unresolved method call: set` because `"set"`/`"insert"` are absent from the
builtin-Dict method whitelist (`is_dict_method_name` at
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:1254`) —
confirmed present at that line, `"set"`/`"insert"` genuinely not listed
(`keys`/`values`/`has`/`contains`/`contains_key`/`get`/`remove`/`delete` are).
That whitelist and the rest of the Dict `.set` dispatch chain are woven through
MIR lowering machinery adjacent to (and, per the 2026-08-02 findings above, in
the Rust seed's Cranelift codegen also inside) files this lane is expressly
barred from touching (`_MirLoweringExpr/switch_operators_calls.spl`,
`mir_data.spl`, `_MirLowering/module_lowering.spl`, and — per repo rules —
`src/compiler_rust/**` entirely, which is where the seed-JIT `nil`-return and
same-module array/tuid silent-noop defects actually live per the refuted
hypotheses above). A same-module fixture also could not be re-run to confirm
current behavior: the self-hosted lane segfaults on trivial Dict-free
hello-world programs per the 2026-08-07 doc (a separate pre-existing defect),
and this lane's `bin/simple` is the Rust seed only (`bootstrap/stage1-3` seed
binaries present, no deployed pure-Simple binary in `bin/`).

Left OPEN. Not a duplicate of `reference_dict_bracket_assign_beats_set_both_engines.md`
(the memory note is about `d[k]=v` racing/beating `.set()` when both apply to
the same key in sequence) — this file's defects are `.set()`'s return value
and cross-receiver dispatch being wrong in the Rust seed's codegen, plus (per
the 2026-08-07 follow-up) `.set()`/`.insert()` not being MIR-lowerable at all
on the self-hosted compiler. Same *family* (Dict write-method routing), two
distinct defects, neither fixable from this lane without touching
off-limits/off-limits-adjacent MIR/codegen internals.
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

## Triage evidence 2026-08-17 (read-only lane; classified by CURRENT SOURCE content, not SHA ancestry)

SPLIT VERDICT.
- Self-hosted-lane companion defect: ALREADY-FIXED. `is_dict_method_name` (src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:1367) now lists `"set"`, and an explicit `if receiver_is_dict and method == "set" and args.len() == 2:` route exists at :1589. (`"insert"` is still NOT in that whitelist — a residual gap.)
- Defect 1 (JIT `.set` return value): STILL LIVE on the deployed seed. Verbatim:
  jit: `ret=` / `nil` / `b=` / `2`
  SIMPLE_EXECUTION_MODE=interpreter: `ret=` / `{a: 1, b: 2}` / `b=` / `2`
  Unchanged from the 2026-08-10 re-verification. Root cause remains in the Rust seed's Cranelift codegen.
