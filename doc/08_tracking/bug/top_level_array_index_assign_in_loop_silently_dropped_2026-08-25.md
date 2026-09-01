# Module-level `arr[i] = arr[i] + 1` inside a top-level loop is silently dropped (2026-08-25)

**Status:** OPEN. **Binary:** Rust seed, `bin/simple run` (JIT and interpreter fallback both).

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
