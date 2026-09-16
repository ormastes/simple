# P0: phase 2 silently drops a loop-carried accumulator update

**Filed:** 2026-09-13
**Lane:** phase 2 only (the pure-Simple Stage 2 compiler). Phase 1 (Rust seed) is correct on **both** its backends.
**Severity:** P0 — wrong answers, exit 0, no diagnostic. This is the worst failure shape a compiler has.

## Symptom

```simple
fn main() -> i64:
    var s = 0
    var i = 1
    while i <= 10:
        s = s + i
        i = i + 1
    print "sum={s} i={i}"
    0
```

| compiler | output |
|---|---|
| phase 1 seed (`run`) | `sum=55 i=11` |
| phase 1 seed, `--backend=cranelift` | `sum=55` |
| **phase 2** | **`sum=0 i=11`** |

The loop executes the right number of times — `i` is 11, so the condition, the
counter update and the back-edge are all fine. Only the accumulator assignment
is dropped. There is no error, no warning, and the process exits 0.

## Trigger

A loop-carried mutation whose right-hand side reads **both** the mutated
variable **and** the loop-condition variable.

| probe | shape | phase 2 |
|---|---|---|
| `a = a + 1` | reads only itself | **correct** |
| `last = i` | reads only the counter | **correct** |
| `s = s + i` | reads **both** | **dropped** |
| `s = s + add(i, i*2)` | both, via a call | **dropped** |
| `xs.push(i)` in a loop | both | **dropped** (`n=0`) |

So neither operand alone is enough; it is the combination.

## Not a backend bug, and not the link shim

- Phase 1 is correct on LLVM **and** on `--backend=cranelift`, so the shape
  itself is not miscompiled by either backend.
- Phase 2 is wrong on both of its own lanes — cranelift-direct and its
  `--backend=llvm` cache object — which places the fault in phase 2's own
  lowering, above the backend.
- The probes are runtime-call-free integer loops, so the hand-link shim used to
  produce a runnable binary cannot account for it.

## Reproduction

Phase 2 cannot finish a `native-build` (see the capsule-receipt defect,
`phase2_file_size_garbage_breaks_capsule_receipt_2026-09-13.md`), so the object
is emitted with `compile --format=smf` and linked by hand:

```sh
. ./scripts/setup/windows-msvc-bootstrap-env.shs
sh build/p2run/build_and_run.sh <path-to-phase2-simple.exe> p2
```

`build/p2run/prog/*.spl` holds the probe set; `zz_mysum.spl` is the case above.
Verified twice, independently, against the same phase 2 artifact.

## Why this matters beyond the one probe

Phase 2 currently produces zero finished binaries on its own, so this defect has
been invisible: every failure so far looked like a *build* failure. It is not.
When the receipt gate is fixed, phase 2 will start emitting binaries that link,
run, and compute wrong values — and a bootstrap that admits such a compiler
would propagate the fault into everything it then builds.

**Admission should stay closed until this is fixed**, independently of the
receipt defect that is currently closing it.

## Related, same lane

- `phase2_file_size_garbage_breaks_capsule_receipt_2026-09-13.md` — `rt_file_size`
  arrives as a pointer-shaped integer, so no `native-build` completes.
- Sampled compile matrices: 19 of 75 `src/lib` files SEGV under phase 2 where
  phase 1 never crashes; 0 of 90 specs compile (the spec DSL does not resolve).
