# Text-index CHARACTER alignment — Stage 1: type-directed census + first real numbers

Stage 1 of
`doc/03_plan/language/text_index_character_alignment_inventory_2026-07-30.md`.
Replaces the carried, INFERRED ~1,193 figure with measured, type-directed
counts for the method-call primitives, and reports precisely where the
tool is blind — those sites are the ones that bite in Stages 2-5.

**It also corrects a significant error in the Stage 0 inventory: the
implementation surface is much wider than the six lanes I listed.**

## The tool

**Placement decision:** extended the **Rust seed's HIR lowering**, not the
pure-Simple linter. Checked first, as instructed: the pure-Simple lint
layer (`src/compiler/35.semantics/lint/`) has no general type inference —
exactly one of its files references `TypeId` — so it cannot tell a text
receiver from an array receiver, which is the entire purpose of this
stage. Receiver `TypeId` is available in
`hir/lower/expr/mod.rs::lower_method_call`, which is also the lane that
runs today.

**Interface:** `SIMPLE_TEXT_INDEX_CENSUS=1` + compile anything. Silent
and free when unset (one `env::var` behind a method-name allowlist).
Records to stdout (the seed drops `eprint` in native builds):

```
TEXTCENSUS<TAB>CLASS<TAB>primitive<TAB>file
```

`CLASS` ∈ `TEXT | ARRAY | DICT | TUPLE | SIMD | ANY | VOID | OTHER |
UNRESOLVED`, from the receiver's `TypeId`, with one pointer-strip so
`T?`/`&T` text receivers classify as TEXT.

Aggregate with: compile each file, `grep '^TEXTCENSUS'`, `awk` by class
and primitive.

## Measured census (PROVED)

Corpus: 150 files from `src/lib/common/**` (non-test), pruned to files
containing at least one syntactic candidate (a file with none cannot emit
a record). All 150 compiled. 2,675 records.

| Receiver class | Records |
|---|---|
| ARRAY | 1,634 |
| TEXT | 721 |
| ANY | 204 |
| OTHER | 116 |

**ARRAY outnumbers TEXT 2.3 to 1.** That is the "cannot be driven by
grep" thesis as a hard number: a syntactic sweep of these same sites
would have mis-migrated the majority.

TEXT-typed by primitive, across 61 distinct files:

| Primitive | TEXT sites | Migration role |
|---|---|---|
| `len` | 439 | changes — **Stage 5 (last)** |
| `slice` | 83 | changes — Stage 3 |
| `char_code_at` | 53 | **MUST NOT CHANGE** (already chars) |
| `bytes` | 44 | stays bytes (escape hatch) |
| `length` | 38 | changes — Stage 5 |
| `substring` | 36 | changes — Stage 3 |
| `char_at` | 26 | **MUST NOT CHANGE** (already chars) |
| `index_of` | 2 | changes — Stage 2 |

Migration-relevant subtotal for this corpus: **598 sites**
(`len`+`length`+`slice`+`substring`+`index_of`). Guard population that
must stay character-indexed: **79 sites**.

## CORRECTION to Stage 0: the implementation surface is wider than listed

Stage 0 named six implementations. That was wrong, and the sibling lane's
discovery of a third `rt_slice` (in the SimpleOS/baremetal tier) prompted
this verification. **Method used:** grep for definitions/declarations of
the runtime symbols themselves (`rt_slice`, `rt_string_len`,
`rt_string_index_of`, `rt_string_char_code_at`) across `.rs`/`.c`/`.spl`
under `src/`, excluding test files, then collapse to directories.

Result (PROVED):

- `rt_slice`: **9 files**, including a **fourth** implementation neither
  Stage 0 nor the sibling lane enumerated —
  `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c` (riscv64
  freestanding boot runtime) — plus `src/runtime/runtime_native.c`,
  `src/runtime/simple_core/core_string.spl`,
  `src/lib/common/string_core.spl`, and the LLVM codegen emitters.
- `rt_string_len`: **56 files** spanning 12+ tier directories
  (`src/app/editor`, `src/compiler/10.frontend/core`,
  `src/compiler/80.driver`, `src/compiler_rust/{compiler,runtime}`,
  `src/compiler_rust/lib/std/src/alloc`, `src/lib/common`,
  `src/lib/nogc_sync_mut/{ffi,fs_driver,db,play}`,
  `src/lib/nogc_async_mut_noalloc/log`, …). Many are `extern fn`
  declarations rather than bodies — which is the point: each is a place
  the ABI contract is restated and could drift.
- `index_of` additionally has **self-hosted compiler** implementations
  (`src/compiler/10.frontend/core/interpreter/_EvalOps/access_literal_assign_eval.spl`,
  `.../cg_expr.spl`, `src/compiler/50.mir/...`), i.e. a whole lane family
  separate from the Rust seed.

  > **Path corrected 2026-08-01.** This originally cited
  > `interpreter/eval_methods.spl`. That file was a DEAD duplicate — every one
  > of its four functions was shadowed by a package-local `_EvalOps` copy — and
  > it was deleted in `f97dfbbb8ee`. The live `index_of` interpreter arm is in
  > `_EvalOps/access_literal_assign_eval.spl`. Incidental citation; the census
  > *count* of lanes is unaffected (one interpreter lane either way), but note
  > that at census time the live arm did **not** honour the 2-arg `start`
  > form — that was only added on 2026-08-01. See
  > `doc/08_tracking/bug/2026-08-01_interpreter_eval_text_method_duplicate_live_subset.md`.

**Consequence for the plan:** "change a primitive across all lanes in one
commit" now requires a per-primitive symbol census *before* each stage,
using the method above, rather than the Stage 0 list. Any stage that
skips it will repeat the silent-clamp class of bug the sibling lane found
in the baremetal `rt_slice`.

## Blind spots (PROVED by controlled probe)

1. **Bracket forms are NOT instrumented.** Hooks in `lower_slice` and the
   generic index path were verified present in source, yet a probe with
   `s[1:2]`, `s[1]` and `xs[0]` emitted **zero** bracket records while
   every method form in the same file emitted correctly — so brackets
   reach HIR by another route (a desugar pass, or the second
   `Expr::Slice` site in `control.rs`). The dead hooks are therefore NOT
   included in this landing. **Stage 4's bracket population remains
   unmeasured and the ~1,193 figure stays INFERRED.** Top follow-up.
2. **`ANY` receivers: 204 records (7.6%)** — untyped/erased receivers the
   tool cannot classify. Exactly the sites that will silently take the
   wrong semantics.
3. **`OTHER`: 116** — generics, user types reusing these method names,
   dynamic dispatch. Per-site triage, not bulk treatment.
4. **Per-file coverage can be partial.** `json/parser.spl` compiled
   cleanly (exit 0, `.smf` emitted) and reported 22 TEXT `len` + 3 TEXT
   `char_code_at`, but its `.substring(` produced no record — consistent
   with only reachable/lowered functions being counted. **All totals are
   lower bounds.**
5. Corpus is 150 of ~625 non-test files in one directory tree, not the
   repo (~4.8 TEXT records/file here).

## Tool vacuity check — hand-verified sample (10 sites: 7 hits, 3 misses)

Probe with known receiver types (`s: text`, `xs: [i64]`), each line
classified by hand before running:

| Site | Expected | Tool | Verdict |
|---|---|---|---|
| `s.len()` | TEXT | TEXT len | hit |
| `xs.len()` | ARRAY | ARRAY len | hit |
| `s.index_of("x")` | TEXT | TEXT index_of | hit |
| `s.substring(1,3)` | TEXT | TEXT substring | hit |
| `s.slice(0,2)` | TEXT | TEXT slice | hit |
| `s.char_at(0)` | TEXT | TEXT char_at | hit |
| `s.char_code_at(0)` | TEXT | TEXT char_code_at | hit |
| `s[1:2]` | TEXT bracket_slice | *nothing* | **miss** |
| `s[1]` | TEXT bracket_index | *nothing* | **miss** |
| `xs[0]` | ARRAY bracket_index | *nothing* | **miss** |

Classification accuracy on what it sees: 7/7, including the text-vs-array
discrimination that matters. No false positives. Coverage gap: all
bracket forms.

## Does this change the recommended stage order?

**No — and it strengthens two choices with data:**

- `index_of` has only **2** TEXT sites here, so Stage 2 is nearly free;
  first position is now justified by cost as well as data-flow.
- `len`/`length` is **477 of 598** migration-relevant sites (80%),
  confirming it must stay **last** — it is the loop bound for every scan.
- Stage 4 gains a prerequisite: instrument the real bracket route before
  planning against an unmeasured population.
- Every stage gains the per-primitive symbol census above.

## Perf baseline update (toolchain changed under us)

The deployed compiler was swapped to the 154MB LLVM-linked build. The
Stage 0 lexer baseline was measured on the previous **no-LLVM** binary,
so both are recorded to keep later regressions attributable:

| Binary | `lex src/lib/common/json/parser.spl` (601 lines), warm |
|---|---|
| previous, no-LLVM | 0.03s, 0.03s |
| current deployed, LLVM-linked | 0.02s, 0.02s, 0.02s |

Method unchanged: `/usr/bin/time -f wall=%e <binary> lex <file>`,
consecutive warm runs. **Compare future numbers only against the
LLVM-linked row.**

## Cross-lane constraints carried forward

- `simple test` never routes through cranelift/JIT even with the env var
  set: no stage touching JIT-visible behavior can be vacuity-proven via
  the test lane — use `bin/simple run` drivers, as with the
  optional-payload and mixed-tuple fixes.
- Known silent JIT miscompile: a 2+-hop chain ending in `.to_i64()`
  appearing twice in one function returns garbage exactly 32 apart, no
  fallback marker. A migrated primitive consumed through that shape will
  look wrong for reasons unrelated to the migration.
- Negative **step** is unsupported and now implemented across three
  engines (`0d35b510fb2`); negative **indices** stay legal. No primitive
  change may make a negative step silently do something.

## PROVED vs INFERRED

PROVED: tool placement rationale (linter type-inference absence checked
in source); every census number (single run, 150 files, all compiled);
classification accuracy and all three bracket misses (controlled probe,
hand-known types); the wider implementation surface incl. the riscv64
`rt_slice` (grep over definitions, method stated above); both lexer rows.
INFERRED: that partial per-file coverage is reachability-driven (symptom
fits; lowering path not traced); that brackets are handled by a desugar
pass or the `control.rs` site (two candidates, unconfirmed); that the
~4.8 records/file rate extrapolates beyond `src/lib/common`; the still
carried ~1,193 bracket figure; that the 56 `rt_string_len` files are
mostly declarations rather than independent implementations (spot-checked
only).
