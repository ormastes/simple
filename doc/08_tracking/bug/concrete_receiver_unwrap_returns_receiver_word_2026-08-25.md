# `.unwrap()` on a CONCRETELY-typed class receiver returns a pointer-shaped word, not the field

- **Date:** 2026-08-25
- **Lane:** lane-fast-oracle
- **Status:** OPEN — BLOCKED on host tooling for empirical re-verification (2026-11-11, lane ne5); fixing commits are compiled into the refreshed seed, but the oracle gate cannot run on this Windows host.
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

## 2026-11-11 addendum (lane ne5)

**Status: BLOCKED (keep OPEN) — fixing commits are compiled into the refreshed
seed; empirical re-verification of this row's gate is not possible on this
host.**

What is established (triage on release/1.0.0 tip):

- The refreshed tracked seed (`bin/simple.exe`, 2026-11-11 build, build-commit
  `0791c2b7f4a7`) provably contains the fix family for this defect class; all
  four are ancestors of the seed build commit AND of release tip:
  - `09b9c429c972` "never bind a bare Optional/Result helper to a lone user
    method" (the lone-user-method same-FuncId shortcut this row's hijack is an
    instance of),
  - `7e8e1748490e` "bare Optional/Result helpers must not suffix-rebind to a
    user method",
  - `28852ec7e3d6` "close the Cranelift twin of the qualified enum-helper
    rebind" (the cranelift-backend half of this row's divergence),
  - `efafcb91aed9` "route the LLVM unwrap family to the flat-nullable-aware
    helpers".
- The gate `scripts/check/check-erased-receiver-unwrap-oracle.shs` still
  classifies this row's `hijack_probe` as the discriminator case (selftest
  cases 10-13).

What blocks verification here (Windows Git Bash host, worktree
simple-p3-ne5-20261111):

- `bin/simple.exe native-build --backend=cranelift <fixture> -o <bin>` writes
  its full build log (terminating with the workaround-coverage advisory) and
  then NEVER EXITS; no output binary appears. Measured: a single fixture build
  sat past 280 s (killed by `timeout` with rc 124); the full oracle's four
  fixture builds each stalled the same way (logs byte-identical at 913553
  bytes, processes unkillable by MSYS `timeout`, requiring `taskkill /F` on the
  WINPID). The gate was calibrated on Linux (~25-55 s per fixture build); on
  this host it cannot produce a verdict. This hang is itself a host-level seed
  defect worth a separate record — noted here, not chased (out of lane scope).

Exact grant to close this row:

    # on a Linux host with a Linux seed binary (or WSL):
    cd <repo root>
    sh scripts/check/check-erased-receiver-unwrap-oracle.shs \
        --seed <path-to-linux-seed> --build-timeout 900

Expected if the fixes hold: `case hijack_probe (probe) ... verdict=OK` and
`PASS — 9 case(s) checked`. If it instead reports THEFT for hijack_probe, the
defect is LIVE and row 1 reopens with a two-line reproducer as before.
