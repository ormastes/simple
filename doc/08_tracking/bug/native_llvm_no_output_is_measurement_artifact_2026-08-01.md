# "Native LLVM binaries produce no output" — CLOSED, measurement artifact

**Date:** 2026-08-01
**Status:** CLOSED — not a codegen defect. Two reproducible measurement
artifacts, plus one real (separate, minor) fail-open flag defect found while
distinguishing them.
**Base sha:** `dfe952d0afae`
**Binary under test:** `bin/release/x86_64-unknown-linux-gnu/simple`,
154,185,152 B. Capability probe
`strings <bin> | grep -c "enum construction: unregistered enum"` → **0**, i.e.
this is the **Rust-built seed driver**, not a bootstrap-stage binary
(`simple.bootstrap-main-stage-2026-08-01.bak` → **2**). Identity established by
probe, never by size or banner.

## The claim

Recorded as *INFERRED, not proved*: native LLVM binaries produce no output,
"needs a bootstrap-profile seed to investigate".

## Verdict: PROVED not real

Native binaries **do** produce output. Source (`hello.spl`, relative path — an
absolute path makes `simple compile` exit 0 without compiling):

```
fn main() -> i64:
    print("HELLO-LLVM-MARKER")
    return 0
```

| # | invocation | artifact | `file` | run |
|---|---|---|---|---|
| 1 | `compile hello.spl --native -o hello_native` | 609,168 B | ELF 64-bit PIE executable | prints `HELLO-LLVM-MARKER`, rc=0 |
| 2 | `compile hello.spl --native --backend=llvm -o hello_nl` | 609,168 B | ELF 64-bit PIE executable | prints `HELLO-LLVM-MARKER`, rc=0 |
| 3 | `SIMPLE_BOOTSTRAP=1 compile hello.spl --native -o hello_bs` | **3,784 B** | ELF 64-bit PIE executable | **prints nothing**, rc=0 |
| 4 | `compile hello.spl --backend=llvm -o hello_llvm` | 4,736 B, mode `rw-rw-r--` | `data` (SMF container, not ELF) | **not executable at all** |

Positive artifact check (`size`, text segment):

| artifact | text | marker string present |
|---|---|---|
| `hello_native` | 582,459 | yes |
| `hello_nl` | 582,459 | yes |
| `hello_bs` | **867** | yes |

Row 3 is decisive and is the likely origin of the whole claim: the vacuous
binary **contains the string** but has 867 bytes of text — the runtime is never
linked, so nothing ever prints it. A `strings`-based or size-based check passes
on it. Only running it, and comparing the text segment against a live control,
separates it from row 1.

## The decoys, distinguished

Every one of these produces the identical observable "no output". They are
different defects (or non-defects) and must not be conflated:

1. **`SIMPLE_BOOTSTRAP=1` vacuous binary** (row 3). 3,784 B here — note the
   previously-recorded figure was 5,608 B, so **the size is not a stable
   fingerprint**; use the text-segment delta (867 vs 582,459) or a run.
2. **`--backend=llvm` without `--native`** (row 4) emits an **SMF object
   container**, not a linked executable, and does not even set the execute bit.
   Running it is impossible; "no output" here is a category error, not a bug.
3. **60 s timeout.** Exit 255 with zero output is the monitor daemon's kill, not
   a crash — `bounded_drain` truncates all evidence and returns −1. Re-run with
   `--timeout 600` before diagnosing. Observed live in this session:
   `bin/simple test <spec>` reported `ERROR: test daemon timed out` at the
   default limit on a spec that needs longer.
4. **Absolute-path no-op compile.** `simple compile /abs/path.spl` exits 0
   without producing anything.
5. **Pre-2026-07-19 hybrid nil-stub era.** Per
   `doc/03_plan/compiler/native_pattern_match_staging.md` §"Correction
   2026-08-01", before `7adbe1359ca` flagged functions were hybrid-stubbed and
   "silently return nil", whose documented symptoms include *"prints nothing"*.
   Any pre-2026-07-19 "native prints nothing" report is CONFOUNDED by this and
   is not evidence of an LLVM defect.

No bootstrap-profile seed was required to settle this.

## Separate real defect found: `--backend=` is unvalidated (fail-open)

`bin/simple compile hello.spl --backend=bogus -o hb` **succeeds**, rc=0,
producing the same SMF output as `--backend=llvm`. And rows 1 and 2 above are
**byte-identical** (`cmp` reports no difference), so `--backend=llvm` is
silently ignored when `--native` is given.

Consequence: **no measurement taken through `--backend=<x>` on this driver has
ever been measuring backend `<x>`.** The original "LLVM backend produces no
output" observation could not have been an LLVM-backend measurement at all.

This is a genuine fail-open flag defect (an unknown value should be rejected,
and an ignored value should say so) but it is a driver-argument bug, not a
codegen bug, and is out of scope for this lane. Filed here so the next lane does
not re-derive it.

## Rule

Never conclude "no output" without separating: vacuous binary
(`SIMPLE_BOOTSTRAP=1`), 60 s timeout, silent interpreter fallback,
absolute-path no-op compile, nil-stub era, and a genuine codegen defect. The
positive check is: `file` reports a statically-linked-or-PIE executable, `size`
shows a text segment comparable to a live control, and the binary actually runs
and prints.
