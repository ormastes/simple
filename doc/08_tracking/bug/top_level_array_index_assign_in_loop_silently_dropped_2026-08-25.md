# Module-level `arr[i] = arr[i] + 1` inside a top-level loop is silently dropped (2026-08-25)

**Status:** FIXED in source on 2026-08-25; manual verification intentionally skipped by user request.
**Binary:** Rust seed, `bin/simple run` (JIT and interpreter fallback both).

## Symptom
```
var hist = [0, 0, 0]
for v in [-1, 4, 7, 2]:
    val bin = ((v % 3) + 3) % 3
    hist[bin] = hist[bin] + 1
print hist            # prints [0, 0, 0]
```
The identical body inside `fn main():` prints `[0, 2, 2]`. A `while` loop at module level shows
the same no-op. No warning, no error — the write is lost.

## Impact
sdoctest blocks are module-level statements, so any README block that mutates a collection by
index in a loop passes the wrong oracle or fails mysteriously (hit in
`examples/08_gpu/simple_cuda_example/20.cuda_intermediate/21.Sync_and_Atomics/README.md`).
Workaround used there: define the mutation inside a `fn` in the block (`>>> fn f():` + `... ` lines).

## Reproduce
`scratchpad` probes `b21b.spl` (top-level, wrong) vs `b21c.spl` (inside fn, right) — 12 lines total.
Likely area: module-level statement execution path in the seed (`compiler_rust/compiler/src/interpreter*` / JIT `ExecCore::run_file_interpreted_with_args`) treating a module-level `var` collection as a copied temporary inside loop bodies (value-semantics COW alias, cf. `code-style.md` rule on collection aliases).

## Root cause and fix

The seed evaluator keeps same-file module values in both its evaluation `Env`
and `MODULE_GLOBALS`. Non-local identifier reads intentionally use
`MODULE_GLOBALS` as authoritative, but the plain `identifier[index] = value`
store path selected the `Env` snapshot whenever it existed and wrote back only
there. The mutation therefore succeeded against an invisible copy while every
subsequent expression read the unchanged global.

`interpreter/node_exec.rs` now distinguishes true locals and owner-qualified
imports from same-file module globals before entering the local-only fast path.
It retains the non-local `Env` entry as a name-precedence snapshot (so a module
collection continues to shadow same-named functions/classes/enums), while
mutating the authoritative array/dict/tuple value in place exactly once. The RHS
and index still evaluate once and in their original order. The first write can
pay the same COW copy as before because that snapshot shares the initial Arc;
the authoritative Arc is then unique and repeated writes remain O(1). Genuine
user aliases retain normal COW behavior. The fix adds no per-write
full-container copy and does not change the public API.

Focused Rust mechanism coverage pins the original top-level loop, local
shadowing isolation, indexed augmented assignment through the same plain-store
path, callable/type name-collision precedence, missing-container failure, invalid
index conversion, and tuple out-of-bounds failure without partial publication.
No tests, builds, benchmarks, SPipe, or optimizer were run for this change, per
the user's explicit no-verification instruction.
