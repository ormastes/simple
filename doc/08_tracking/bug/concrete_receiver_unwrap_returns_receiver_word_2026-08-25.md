# `.unwrap()` on a CONCRETELY-typed class receiver returns a pointer-shaped word, not the field

- **Date:** 2026-08-25
- **Lane:** lane-fast-oracle
- **Status:** OPEN — reproduced and localized to a backend divergence; not fixed
- **Gate:** `scripts/check/check-erased-receiver-unwrap-oracle.shs` is RED on this defect (`hijack_probe`), 81s
- **Backend:** cranelift, Rust seed (`native-build --backend=cranelift`)
- **Severity:** silent wrong value, no diagnostic, exit 0

## Summary

A user-defined class method named `unwrap`, called on a receiver whose type is
**known and local**, returns a large pointer-shaped integer instead of the value
the method body returns. There is no build error and no runtime error: the
program exits 0 with a wrong number.

This is **NOT** the erased-receiver theft tracked in
`stage3_n_modules_zero_segv_mir_lowering_x86_64_2026-08-24.md`. There the
receiver's type is erased and the call is stolen by a receiver-type-blind
name-suffix scan. Here the receiver type is concrete, same-module or explicitly
imported, and the call is not erased at all. Recorded separately so the two are
not conflated.

## Reproduction

Fixtures (already in-tree, added by the oracle lane):

- `test/fixture/erased_unwrap_oracle/decoy_present.spl` — decoy class in the same file
- `test/fixture/erased_unwrap_oracle/xmod_main.spl` — decoy class in a separate module

Both contain:

```
class Dec:
    var v: i64

    fn unwrap() -> i64:
        self.v
...
    var dec = Dec(v: 7)
    print("DECOY=" + dec.unwrap().to_string())
```

Run from the **repo root** (outside it the seed answers `refusing Rust fallback`;
see the oracle record for why that is a cwd artifact, not a policy barrier):

```sh
timeout 900 <seed> native-build --backend=cranelift \
    test/fixture/erased_unwrap_oracle/decoy_present.spl -o /tmp/decoy \
    > /tmp/decoy.log 2>&1
BUILD_RC=$?          # read directly into a variable, never through a pipe
/tmp/decoy
RUN_RC=$?
```

## Observed

| fixture | BUILD_RC | RUN_RC | `DECOY=` | expected |
|---|---|---|---|---|
| `decoy_present.spl` (cranelift) | 0 | 0 | `95601341756065` | `7` |
| `xmod_main.spl` (cranelift) | 0 | 0 | `100373692547745` | `7` |
| `concrete_unwrap_hijack.spl` (cranelift) | 0 | 0 | `CONCRETE_UNWRAP=110153921397409` | `111` |
| same file, `NAME_CONTROL` (cranelift) | 0 | 0 | `NAME_CONTROL=111` | `111` (correct) |
| same source, **default backend** | 0 | 0 | `111` / `222` | correct |

The `NAME_CONTROL` row is the load-bearing one: `Aaa.unwrap_ctl()` has a
byte-identical body to `Aaa.unwrap()` and is called on the same receiver in the
same shape. It returns `111`. The fault is isolated to the method NAME.

Both values are in the heap-pointer range. The callee returns the **receiver**
rather than `self.v` — confirmed by disassembly, see the next section.

In the same binaries the neighbouring erased-receiver `.unwrap()` returns its
correct value (`ERASED_UNWRAP=4242`), so this is not a general breakage of
`unwrap`-named methods, nor of those fixtures' Option handling.

## It is a BACKEND DIVERGENCE, and the callee is identified

Reproduces **only** under `--backend=cranelift`. On the **default** backend the
same source prints `111` / `222` correctly.

Disassembly of the cranelift binary: `nm` shows **no `*_dot_unwrap` symbol at
all**, and the call site reaches **`rt_unwrap_or_self`** — a runtime helper that
returns its argument. That accounts exactly for the pointer-shaped word: the
user-defined `Aaa.unwrap()` is shadowed by builtin `unwrap` routing, and the
builtin hands the receiver straight back.

So the shape is: on cranelift, the builtin `unwrap` routing wins over a
user-defined class method of the same name. It is the INVERSE of the erased-receiver
theft (there a user method is chosen where a builtin should have been).

## Why it matters beyond itself

Any oracle for the erased-receiver defect that asserted only "the binary exited
0" would be contaminated by this defect. That is why
`scripts/check/check-erased-receiver-unwrap-oracle.shs` asserts the specific
sentinel `ERASED_UNWRAP=4242` rather than the exit status.

## Not done here

No investigation, no disassembly, no fix. The lane that found it was building an
instrument for a different defect and deliberately did not chase this one. The
next lane inherits a two-line reproducer and a ~25 s build loop.
