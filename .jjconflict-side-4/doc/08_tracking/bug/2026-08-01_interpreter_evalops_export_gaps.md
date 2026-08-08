# _EvalOps export gaps: `eval_int_method` unreachable, text `.at` missing

**Date:** 2026-08-01
**Status:** FIXED (items 1 and 2); item 3 fixed for `_EvalOps`, QUANTIFIED and left open for the rest of the package
**Filed by:** follow-up from `2026-08-01_interpreter_eval_text_method_duplicate_live_subset.md`
**Area:** pure-Simple interpreter, `_EvalOps` package surface

Three gaps in the live dispatch tree
`src/compiler/10.frontend/core/interpreter/_EvalOps/`. All three share one root
cause: the package `__init__.spl` uses **explicit export lists**, so nothing in
`_EvalOps` is visible to an out-of-tree importer until somebody types its name.

## Engine provenance

Every behavioural number below came from the **pure-Simple interpreter**, driven
through `core_interpret_expr` by `scratchpad/gap3_probe.spl` with the Rust seed
as **HOST only** (`src/compiler_rust/target/bootstrap/simple run`, 32 MB build
present on this machine — note this is NOT the 154 MB canonical LLVM build; it
is adequate here because it only has to compile the driver, and the values under
test are computed by the working-copy `.spl` interpreter it compiles).

Spec results came from the **Rust seed test runner**
(`src/compiler_rust/target/bootstrap/simple test`) — the only engine the suite
reaches; `bin/simple` has no `test` subcommand at HEAD.

## 1. `eval_int_method` was exported by NOBODY

`eval_int_method` is defined at `_EvalOps/call_method_eval.spl:1053` and called
at `_EvalOps/call_method_eval.spl:614` (the `kind == VAL_INT` arm of the per-kind
dispatch). It was named by **neither** `__init__.spl` **nor** `eval_ops.spl`.

Consequence: any out-of-tree module that imported
`compiler.frontend.core.interpreter.*` and reached `core_interpret_expr` did not
merely mis-evaluate int methods — it **failed to link**:

```
--- item 1: int methods ---
error[E1002]: function `eval_int_method` not found
  = help: check the function name or import the module that defines it
```

That is the whole driver dying before its first assertion, so it also masked
item 2 entirely.

Pre-existing: `eval_int_method` never lived in `eval_methods.spl`, the file
deleted in `f97dfbbb8ee`, so this is not fallout from that deletion.

**Fix:** named in `__init__.spl`, together with the six other `_EvalOps`
functions that had the same problem (below). After the fix:

```
(65).chr()      => kind=text  txt='A'
(97).to_char()  => kind=text  txt='a'
(42).to_text()  => ERROR=no method 'to_text' on int
```

`to_text` on an int is genuinely unimplemented — `eval_int_method` has exactly
one arm (`chr`/`to_char`). It **fails loudly** via `eval_set_error`, which is the
correct behaviour and is now pinned by a spec example. Recorded here as a known
narrow surface, not fixed: implementing int methods is a separate change.

## 2. Text `.at` was absent from the live text method table

`at` had no arm in `eval_text_method` — not in the live copy, and not in the
`eval_methods.spl` copy deleted on 2026-08-01 either. So this is a genuine gap,
not a regression from that deletion.

A missing arm falls through to `eval_set_error(...)` + `-1` (`VAL_NONE`), which
reads back as **the receiver unchanged** for text. Measured before the fix:

```
"abcdef".at(0)  => kind=nil  txt='abcdef'
"abcdef".at(2)  => kind=nil  txt='abcdef'
"abcdef".at(99) => kind=nil  txt='abcdef'
```

Arrays DO have `.at` (`_EvalOps/call_method_eval.spl:937`), so text and arrays
diverged, and they diverged the *opposite* way from the divergence recorded in
`array_at_method_missing_dash_path_2026-07-20.md` (there it is the **seed** that
lacks array `.at` while the pure-Simple interpreter has it).

### Semantics: byte-indexed, flat-Option — deliberately NOT the seed's

Surveyed before choosing:

| lane | index basis | out of range |
|---|---|---|
| seed `src/compiler_rust/compiler/src/interpreter_method/string.rs:368` (`"char_at" \| "at"` share one arm) | character | `""` |
| C runtime `rt_string_char_at` (`runtime_native.c:2393`), reached from `rt_index_get:5280`, i.e. what `s[i]` lowers to on native/JIT | byte | `nil` |
| live array `at` (`call_method_eval.spl:937`) | n/a | `nil` (flat None) |
| pure-Simple codegen / MIR | **no `at` arm at all** — `grep '"at"' src/compiler --include=*.spl` outside `interpreter/` returns nothing | — |
| **this arm** | byte | `nil` (flat None) |

Chosen to match the **runtime** on both axes:

1. `.at` is this codebase's bounds-checked Option accessor. Array `.at` returns
   flat-None past the end — under the FLAT encoding the element *is* its own
   `Some` and `nil` is `None`; there is no `VAL_ENUM` in this interpreter. 250+
   call sites `match x.at(i)` as `Some`/`None`. A text `.at` returning `""`
   would make every one of them take the `Some` branch on an out-of-range read.
2. Byte indexing keeps `at` composable with `len` / `index_of` / `slice` /
   `char_at`, which all hand out byte offsets here, and keeps the interpreter in
   agreement with native/JIT. Interpreter/native agreement is the property that
   matters for a compiler lane — the same reasoning already recorded on
   `char_at` in `2026-08-01_interpreter_char_code_at_byte_indexed.md`.

So this arm agrees with the C runtime on both axes and diverges from the seed on
both. **Do not "fix" it toward the seed.** Recorded inline at the arm as well.

After the fix (pure-Simple interpreter):

```
"abcdef".at(0)   => kind=text  txt='a'
"abcdef".at(2)   => kind=text  txt='c'
"abcdef".at(5)   => kind=text  txt='f'
"abcdef".at(6)   => kind=nil
"abcdef".at(99)  => kind=nil
"abcdef".at(-1)  => kind=nil
"".at(0)         => kind=nil
"café,".at(3)    => kind=text, one byte (0xC3, the LEAD byte of é)
[10,20,30].at(1) => kind=i64 20      (array control, unchanged)
[10,20,30].at(9) => kind=nil         (array control, unchanged)
```

A no-arg `"x".at()` raises `at() requires an index argument` rather than
returning `""`. `char_at`'s older no-arg behaviour (return `""`) is the
silent-default shape this campaign keeps having to undo; the new arm does not
copy it.

## 3. `__init__.spl` explicit export lists — SYSTEMIC, quantified

`eval_ops.spl` re-exports the split package with
`export use ..._EvalOps.call_method_eval.*` / `...access_literal_assign_eval.*`,
so anything added to `_EvalOps` is automatically visible to importers of
`eval_ops`. But `__init__.spl` — what `use compiler.frontend.core.interpreter.*`
resolves — uses explicit `export NAME, NAME` lists and does **not** inherit that
wildcard. A function added to `_EvalOps` is therefore invisible to every
out-of-tree importer until someone remembers to list it, and the failure
surfaces as a link error in an unrelated file, far from the edit that caused it.

### `_EvalOps` — FIXED

7 of 33 top-level functions were unexported:

```
eval_dict_lit  eval_enum_variant_access  eval_enum_variant_call
eval_host_gpu_lane_call  eval_interpolation_segments  eval_int_method
eval_tuple_lit
```

All 7 are now named in `__init__.spl`. `_EvalOps` is at **0/33 unexported**, and
a spec example scans the two `_EvalOps` files mechanically so a future addition
cannot slip through.

### The rest of the package — OPEN

Anchored count over `src/compiler/10.frontend/core/interpreter/`, matching
`^fn NAME(` against every name on an `export` line of `__init__.spl` (token
anchored, so an export of `eval_dict_literal` does not satisfy a definition of
`eval_dict_lit`):

**171 of 437 top-level functions (39%) are not exported.**

Five modules are **100% unexported** — nothing they define can be reached
through `use compiler.frontend.core.interpreter.*`:

| module | unexported / total |
|---|---|
| `module_loader_lazy.spl` | 24 / 24 |
| `load_session_cache.spl` | 23 / 23 |
| `compiled_module_adapter.spl` | 10 / 10 |
| `test_interp.spl` | 8 / 8 |
| `intern.spl` | 4 / 4 |

and the largest partial gaps are `eval.spl` (24/32), `resolve.spl` (23/27),
`eval_stmts.spl` (15/16), `module_loader_resolve.spl` (12/14),
`module_loader_core.spl` (11/24), `jit.spl` (7/26).

This is why a driver that only wants `core_interpret_expr` needs **13 explicit
wildcard imports** (`lexer*`, `parser*`, `ast*`, `types`, `monomorphize`,
`frontend.core.*`) before it will link. Several lanes have now paid that cost
independently.

**NOT fixed here**, deliberately: some of those 171 are genuine internals
(Simple has no visibility modifier, so "top-level `fn`" over-counts the intended
public surface), and mass-exporting a package this size is a change that needs
its own review. The right fix is probably to give `__init__.spl` the same
`export use <module>.*` form `eval_ops.spl` already uses, module by module, with
a real internal/public split where one exists. Scoped as a follow-up.

## Regression coverage

`test/01_unit/compiler/interpreter/evalops_export_and_text_at_spec.spl` — 7
examples, all green on the Rust seed test runner.

### Why it is structural, and what that costs

A behavioural spec — one that imports the interpreter and drives
`core_interpret_expr` inside `it` blocks — was written first and **does not
work**, for two independent reasons, both pre-existing and both unrelated to the
arms above:

| placement | outcome |
|---|---|
| under `test/` (`test/01_unit/compiler/interpreter/`, and also `test/01_unit/compiler/`) | does not compile: `error: semantic: variable 'cache_initialized' not found` — a module-level `var` in `interpreter/value.spl:48` |
| identical file outside `test/` (scratchpad path) | compiles, runs 7 examples, 4 pass / 3 fail with `semantic: array index out of bounds: index is 263 but length is 0` — the interpreter value pool read as EMPTY mid-run |

Both are the known cross-module module-level-global defect
(`reference_jit_cross_module_global_import_reads_wrong`,
`reference_module_level_let_not_preregistered_order_dependent`). The
tree-position dependence — the same bytes compiling at one path and not another
— is the sharper half and is worth its own investigation.

**Consequence to be honest about:** the behavioural evidence in this document
comes from the standalone driver and is transcribed, not re-executed by CI. The
spec is a regression *pin* on the file that runs, in the shape settled on by
`text_byte_at_dispatch_spec.spl` and `option_result_method_dispatch_spec.spl`.
The export-completeness example is mechanical rather than a hand-written name
list, and it self-checks (it asserts the scanner finds `eval_int_method` and
`eval_text_method` against an empty export list first), so it cannot pass
vacuously.

### Proof the spec can fail

Each guard sabotaged once, observed red, restored. Engine: Rust seed test runner.

| sabotage | result |
|---|---|
| baseline | `7 examples, 0 failures` |
| drop `export eval_int_method` from `__init__.spl` | `3 failures` — export-completeness, `eval_int_method` reachability, and per-kind routing |
| text `.at` out-of-range → `val_make_text("")` (the seed convention) | `1 failure` — *"returns flat None from text .at out of range, matching array .at"* |
| no-arg `.at` returns `val_make_nil()` instead of erroring | `1 failure` — *"fails LOUDLY when text .at is called with no index"* |
| strike `interpreter_method/string.rs` from the divergence table | `1 failure` — *"documents text .at as a deliberate divergence from the seed"* |
| restored | `7 examples, 0 failures` |

The `.at` sabotage was also run **two-directionally through the interpreter**, in
the same style that proved `eval_methods.spl` dead: with the out-of-range return
changed to `val_make_text("")`, the driver's `"abcdef".at(99)` flipped from
`kind=nil` to `kind=text txt=''`. The arm is on the live dispatch path.

## Adjacent red specs — PRE-EXISTING, not caused by this change

Both verified by re-running against a working copy with this change backed out.
Neither is fixed here.

- **`text_index_of_start_spec.spl` — 1 of 3 failing.** It pins the marker
  `if method_name == "index_of":`, which no longer exists: `f97dfbbb8ee` merged
  that arm into `if method_name == "index_of" or method_name == "find" or
  method_name == "find_str":`. `index_of` returns `-1`, and
  `expect(branch_start).to_be_greater_than(-1)` fails. A stale structural marker
  left by that lane; the assertions after it are still the right assertions.
  **Note the trap for anyone re-measuring: `git HEAD` is well behind this working
  copy, so a HEAD-based baseline shows this spec GREEN and makes it look like a
  fresh regression.**
- **`array_at_option_accessor_spec.spl` — 5 of 5 failing**, every one with
  `semantic: method 'at' not found on type 'array'`. That spec is behavioural and
  runs on the seed engine, which has no array `.at` — exactly the gap
  `array_at_method_missing_dash_path_2026-07-20.md` filed and holds a patch for.
  It is a seed gap, not a pure-Simple one.

Green and unchanged: `text_byte_at_dispatch_spec` (4/4),
`option_result_method_dispatch_spec` (6/6),
`text_char_code_at_codepoint_spec` (3/3).

## Follow-ups filed by this document

1. `eval_int_method` implements only `chr`/`to_char`; every other int method
   errors. Loud, but narrow.
2. The remaining **171/437** unexported interpreter functions, and the five
   fully-unexported modules.
3. A spec that imports the interpreter and calls `core_interpret_expr` compiles
   outside `test/` and not inside it. Same bytes, different tree position.
