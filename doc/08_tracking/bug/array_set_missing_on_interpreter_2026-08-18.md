# `[T].set(i, v)` is missing on the interpreter (present in codegen)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Status: OPEN
- Filed: 2026-08-18
- Severity: medium — silently splits `run`/`test` semantics for a documented array method

## Symptom

```
semantic: method `set` not found on type `array` (receiver value: [5, 3, 1, 4, 2])
```

Reproduced on the Rust seed with both `bin/simple test` and
`SIMPLE_EXECUTION_MODE=interpreter bin/simple run`:

```spl
fn main():
    var a: [i64] = [5, 3, 1]
    a = a.set(0, 9)          # -> semantic: method `set` not found on type `array`
```

`a.sort()` on the same receiver works, so this is a per-method gap, not a
missing array method table.

## Why it is a product defect, not spec misuse

`set` is wired on the codegen paths and therefore compiles and runs there:

- `src/compiler_rust/compiler/src/codegen/llvm/functions.rs:2918`
  — `("Array" | "array", "set") => Some("rt_index_set")`
- `src/compiler_rust/compiler/src/codegen/instr/methods.rs:383`
  — `("Array", "set") | ("array", "set")`

The interpreter has no counterpart, so the same source is accepted by one
engine and rejected by the other. This is the same engine-divergence family
tracked in `run_vs_test_harness_divergence_2026-07-28.md`, except here the
interpreter is the deficient side.

## Discovery

`test/perf/tauri_equiv/report_spec.spl` used an in-place insertion sort built on
`.set`. Its "sorts descending input" example aborted with the error above, while
"handles already-sorted input" passed vacuously because the swap branch never
ran.

## Workaround in place

The spec's `_sort_ascending` helper was rewritten as a selection sort that only
indexes and pushes, plus defect-class examples covering length preservation,
duplicates, and empty input, so the vacuous-pass path is closed.

## Unblock condition

Add `set` to the interpreter's array method dispatch (mapping to the same
index-set semantics as `rt_index_set`), then revert the helper in
`test/perf/tauri_equiv/report_spec.spl:61` to the in-place form and confirm it
still passes. A seed rebuild is required to verify; the lane that found this
was forbidden from rebuilding `bin/simple`.


## Fixed 2026-11-03

Added `set` to the seed interpreter array mutators (`ARRAY_MUTATING_METHODS`, `apply_array_mutation_in_place`,
and the three arg-evaluation sites in `interpreter_helpers/patterns.rs`). Writes back like `push` (var binding,
class field, module global). Negative index counts from the end (as `rt_array_set`); out of range raises
`E3002` (codegen's `rt_index_set` returns false silently; interpreter fails closed instead).
Spec: `test/01_unit/interpreter/array_set_method_spec.spl` (5/5; 5/5 failed before).
Status: fix-implemented-partial. Remaining gap: JIT lane (`SIMPLE_EXECUTION_MODE=jit`) still reports `Method 'set' not found on type 'Array'`; interpreter lane is fixed.

## 2026-11-04 fix: return value now matches native `rt_array_set` (bool)

The mutator existed (093e83cb8e7) but returned the array and raised an error when out of range,
unlike native `rt_array_set` (`bool`, false on invalid index). `apply_array_mutation_in_place`
(`interpreter_helpers/patterns.rs`, "set" arm) now returns `Some(Bool(true/false))`, no error, no mutation
on out-of-range. All three write-back callers already use `Some(elem)` as the expression result.

- `test/01_unit/language/array_set_spec.spl`: before 0/5, after 5/5.
- `test/01_unit/interpreter/array_set_method_spec.spl` (reassigning-form case changed to bool result): before 2/7, after 7/7.
- Regression sweep (24 array/index/push/list specs under language and compiler/interpreter): no before-pass/after-fail.

## 2026-11-05: JIT/native gap CLOSED on release/1.0.0 (`c3b2271c310`)

The interpreter lane (above) was already in this branch's ancestry, but the
erased compiled-lane dispatch still aborted. `a.set(0, 9)` on
`var a: [i64]` lowers to `MethodCallStatic { func_name: "Array.set" }`
(verified via `SIMPLE_DUMP_MIR=main`), which both the Cranelift/JIT name-keyed
table (`codegen/instr/closures_structs.rs`, `"set" if args.len() == 2 =>
"rt_collection_set"`) and the LLVM erased fallback
(`codegen/llvm/functions.rs`) funnel into the runtime's `rt_collection_set`
— and that function deliberately rejected Array receivers with a loud
"Method 'set' not found on type 'Array'" abort (a decision, with pinned
tests, that predated the interpreter's 2026-11-03 `.set` implementation and
was left stale by it).

Fix (worktree `work/seed-interp-fixes-20261105`):
`src/compiler_rust/runtime/src/value/collections.rs::rt_collection_set` is
now receiver-dispatched like its sibling `rt_collection_remove`: Dict keeps
its fluent receiver result (unchanged); **Array routes to
`rt_array_set(receiver, index, value)` and returns
`RuntimeValue::from_bool(...)`** — negative index counts from the end,
out-of-range returns false with NO mutation, exactly the interpreter's
`apply_array_mutation_in_place` "set" arm and codegen's
`("Array"|"array","set") => rt_index_set` contract. Tuple and every other
receiver keep the loud method-not-found path (the interpreter has no
`tuple.set` either — deliberately out of scope).

TDD evidence (new test first, watched it fail, then fixed):

- BEFORE fix — `cargo test -p simple-runtime --release --lib collection_set`:
  `erased_array_set_mutates_in_place_and_returns_bool` FAILED; child exited
  70 with `Runtime error: Method 'set' not found on type 'Array'`.
- AFTER fix — all 6 `collection_set_tests` PASS, including the new
  `erased_array_set_accepts_child` (in-range mutate→true, negative index,
  OOB both sides→false + no mutation).
- The two tests that pinned the OLD loud-rejection contract for arrays were
  updated: `array_set_rejection_is_loud`/`array_set_rejection_child`
  (array variants) removed; `array_and_tuple_set_keep_their_method_not_found_identity`
  narrowed to `tuple_keeps_its_method_not_found_identity`. Tuple rejection
  tests unchanged and green.

End-to-end repro (`var a: [i64] = [5,3,1]`; set(0,9) / set(-1,7) /
set(10,99) / set(-10,42)), seed built from this branch:

| mode | before | after |
|---|---|---|
| `SIMPLE_EXECUTION_MODE=interpret` | `true [9,3,1]` / `true [9,3,7]` / `false` / `false` (already fixed) | identical |
| `SIMPLE_EXECUTION_MODE=jit` | **abort: `Method 'set' not found on type 'Array'`** | identical to interpret |
| native default | **abort: `Method 'set' not found on type 'Array'`** | identical to interpret |

2026-11-05 parallel-review follow-up (P1): the Array arm initially decoded the
index with `as_index_i64().unwrap_or(-1)`, so a non-integer key on the erased
compiled lane normalized to `len-1` and silently overwrote the LAST element
(`arr.set("k", v)` returned true). Fixed to return `false` with no mutation on
a non-integer key, matching `rt_index_set`'s `None => false` contract. Pinned
by child-test assertions in `erased_array_set_accepts_child` (text key, float
key, last element intact) — failed pre-fix, pass post-fix; the full
`collection_set_tests` module is 6/6 and the three-engine repro output is
unchanged.

Specs with the rebuilt seed: `test/01_unit/language/array_set_spec.spl`
5/5 PASS, `test/01_unit/interpreter/array_set_method_spec.spl` 7/7 PASS
(both previously passing under interpret only; the array-set examples in
them now also behave identically on jit/native). Rust: all 6
`collection_set_tests` plus the value/dict-entry unit tests pass; the
adjacent executor/thread tests pass in isolation. The FULL
`simple-runtime` lib suite could not complete in this macOS worktree
environment — it hangs in `cache_host_authority_v14` tests and later
SIGBUSes under full-suite load; BOTH symptoms reproduce identically with
the pre-fix `collections.rs`, so they are pre-existing environment issues,
not regressions from this change. Known unrelated pre-existing failure:
`test/01_unit/language/dict_items_for_loop_spec.spl` (probe-child
`PROBE_DONE` missing on macOS; the spec never calls `.set`).

Status: FIXED on all three engines (interpret, jit, native).

## 2026-11-10 P3 triage (work/p3-interp-20261110) — SUPERSEDED, interpreter lane verified

Re-verified on the deployed Windows Rust seed (`bin/simple.exe`, 34 MB 2026-11-10
worktree build), cwd = worktree root:

- `test test/01_unit/interpreter/array_set_method_spec.spl` → 7/7 PASS.
- `test test/01_unit/language/array_set_spec.spl` → 5/5 PASS.
- Three-engine repro (`set(0,9)`/`set(-1,7)`/`set(10,99)`/`set(-10,42)`):
  `SIMPLE_EXECUTION_MODE=interpret` prints exactly the fixed table
  (`true [9,3,1]` / `true [9,3,7]` / `false` / `false`).

Interpreter lane: FIXED and green on the deployed seed. JIT lane on this host
still aborts `Method 'set' not found on type 'Array'` — the deployed Windows
seed binary predates `c3b2271c310`; the fix itself IS in source and branch
ancestry (`rt_collection_set` routes Array → `rt_array_set` at
`src/compiler_rust/runtime/src/value/collections.rs:2811-2837`, verified read).
Residual action is a seed redeploy for jit/native, not a code change
(same class as `deployed_seed_binary_missing_var_roots_cache_fix_2026-09-13`).
