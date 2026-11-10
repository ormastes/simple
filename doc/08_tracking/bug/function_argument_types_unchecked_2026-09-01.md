# Function argument types are not checked — a `text` passed to an `i64` parameter runs
## Open 2026-11-11 — LIVE, re-confirmed on seed 46fe8f6b6def (lane ne10; see addendum)

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-09-01
**Found by:** workstream I; **independently reproduced by the parent session.**
**Status:** OPEN — re-confirmed LIVE 2026-11-11 by lane ne10 (all three repro forms still run,
exit 0). Blocks goal G7 (typed addresses) in
`doc/03_plan/hardware/nvme_complete_fw_mdsoc_offload_master_plan.md`.

## Reproduction (parent session, verbatim)

```simple
fn takes_i(x: i64) -> i64:
    x + 1

fn main():
    print("A=" + takes_i(41).to_text())
    print("B=" + takes_i("hello").to_text())
    return ()
```

`bin/simple run` output:

```
A=42
B=2402438622338
```

No error, no warning, exit 0. `B` is a raw string pointer with 1 added to it.

## Scope caveat, stated because it changes who must fix it

`bin/simple` here is the **Rust bootstrap seed** — it prints
`WARNING: this Rust-built Simple binary is a bootstrap seed only`. Whether the
pure-Simple self-hosted compiler also fails to check is **NOT established**:
retesting is blocked by the bootstrap redeploy failure. Do not close this bug on
a seed-only fix, and do not widen it to a self-hosted claim without the retest.

## Why it blocks G7

The typed-address plan converts ~1,575 address sites to per-layer newtypes so
that passing a `Ppn` where an `Lba` is expected becomes a compile error. On the
measured behaviour, **a wrapper type is documentation and a grep target, not a
guarantee** — the compiler will not reject the swap. Workstream I additionally
reports that `newtype Lba` accepts a `Ppn` and accepts a bare `5`, and that
single-field structs (the `nd_types.spl` pattern) accept a wrong-typed struct.

`bin/simple lint` reports `Lint passed: all files clean` on the above, and
`SIMPLE_JIT_STRICT=1` also passes.

## Consequence for the plan

A nominal argument-type check is **on the critical path for G7**. The interim
substitute is a fail-closed textual ratchet gate
(`check-typed-address-algebra.shs`, baseline 202 bare-`i64` address parameters in
`fw/`), mirroring how workstream B substitutes a `use`-graph gate for the missing
`call(...)` pointcut. The gate constrains new code; it cannot make the types real.


---

## 2026-11-11 addendum — lane ne10 (P3 traverse, batch ne10)

**Verdict: LIVE — keep OPEN.** Re-confirmed verbatim on tracked seed `bin/simple.exe`
build-commit `46fe8f6b6def` (seed-smoke: `SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe
./bin/simple.exe run <repro> --mode=interpreter --no-cache`).

- **Doc repro unchanged:** `takes_i("hello")` against `fn takes_i(x: i64)` prints `A=42` and
  `B=3904863579906` (a raw string pointer + 1; the pointer value differs from the 2026-09-01
  run, the defect shape is identical), no error, no warning, exit 0.
- **G7 blocker claims also re-confirmed LIVE** on this seed:
  - `takes_lba(Ppn(7))` against `fn takes_lba(x: Lba)` runs and exits 0 (`newtype Lba` accepts a
    `Ppn`).
  - `takes_lba(5)` against `fn takes_lba(x: Lba)` runs and exits 0 (accepts a bare `5`).
- **Scope note:** the fix is a nominal argument-type check in the compiler itself — the G7
  critical path named above. That is owner-lane compiler work, not P3-traverse scope; no seed
  or self-hosted change this lane alters it.
