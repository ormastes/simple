# Module-level `arr[i] = arr[i] + 1` inside a top-level loop is silently dropped (2026-08-25)

## Update 2026-09-13 — re-measured, still OPEN, and MUCH broader than array-index writes

Re-reproduced on Windows with the Rust seed `build/vt4/bootstrap/simple.exe`
(`simple run <file>`). Confirmed still live. Three corrections to the original
characterisation, all MEASURED:

1. **It is not about array-index writes.** A plain scalar `n = n + 1` in a
   top-level loop body is dropped the same way. Array indexing is incidental.
2. **The whole loop is discarded, not just the write.** For
   ```
   var n = 0
   var i = 0
   while i < 3:
       n = n + 1
       i = i + 1
   print "n={n} i={i}"          # measured: n=0 i=0
   ```
   `i` is also 0 afterwards, yet the program *terminates immediately*. If the
   writes were merely lost the loop could never exit. So the loop body runs
   against a discarded copy of the module scope — this is a scope/snapshot
   defect in module-level statement execution, not dead-store elimination.
3. **It is position/shape sensitive, which is why it looked intermittent.**
   Measured on the same binary, same session:

   | program (all top level) | printed | correct? |
   |---|---|---|
   | `var n=0` + `for x in [1,2,3]: n=n+1` + `print n` | 3 | yes |
   | `val a=[1,2,3]` + `var n=0` + `for x in a: n=n+1` + `print n` | **0** | no |
   | `var n=0` + `val a=[1,2,3]` + `for x in a: n=n+1` + `print n` | **0** | no |
   | `var n=0` + `var i=0` + `while i<3: n=n+1; i=i+1` + `print n` | **0** | no |
   | `var n=0` + `var i=0` + `while i<3: i=i+1` + `print i` | 3 | yes |
   | `var n=0` + `var j=0` + `var i=0` + `while i<3: n=n+1; j=j+2; i=i+1` | n=3 j=6 i=3 | yes |

   A single-declaration program is correct; adding a second top-level
   declaration flips it wrong; adding a third flips it right again. Any
   reduction that "simplifies" the repro can therefore make the bug vanish —
   note this before declaring it fixed.
4. **Identical inside a function.** `fn main(): var n=0; for x in [1,2,3]:
   n=n+1; print n` prints 3. The defect is confined to module scope.
5. **Lane-independent within the seed.** Same wrong answer with the default
   JIT, `SIMPLE_NO_JIT=1`, and `SIMPLE_EXECUTION_MODE=interpret`.

**Not fixed here:** the fix lives in `src/compiler_rust/**`, which was
off-limits during this pass (a bootstrap was running and editing Rust sources
aborts it). Entry stays OPEN with a sharper repro.


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
