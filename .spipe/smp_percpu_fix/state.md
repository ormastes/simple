# Lane SMPFIX — per-CPU array indexing defect

Status: FIXED (both engines green)
Date: 2026-07-27
Binary used: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`
(Rust bootstrap **seed** — it prints the seed warning banner; all verdicts below
are seed verdicts.)

## Symptom

`test/01_unit/os/kernel/smp/smp_spec.spl` — 10 of 14 examples failed with
`semantic: array index out of bounds: index is 1 but length is 1`
(and `index is 5 but length is 1` for the offline-CPU example). Only the two
examples that never touch a CPU id >= 1 passed.

## Root cause — engine defect, surfaced by percpu_init's shape

**A module-global written inside a function is NOT observable to any helper that
function subsequently calls. The write only commits when the writing function
returns.** Applies to arrays *and* scalars, in both JIT and interpreter, and only
inside the spec-runner execution context (a plain `fn main()` caller behaved
correctly, which is why this hid for so long).

Minimal repro (probe module, since deleted):

```
var gc_arr: [PE] = []
var gs: u32 = 0u32
fn nested_len()    -> u32: gc_arr.len().to_u32()
fn nested_scalar() -> u32: gs
fn probe_c_init():
    var t: [PE] = []; ...4 pushes...
    gc_arr = t
    gs = 7u32
    print(gc_arr.len())      # 4   <- own frame sees the write
    print(nested_len())      # 0   <- callee does NOT
    print(nested_scalar())   # 0   <- scalars too
# after probe_c_init returns, the caller sees len 4 correctly
```

`percpu_init` tripped exactly this: it filled `g_percpu` with 32 entries and then
called `percpu_store_entry(0u32, ..)` to write the BSP entry. `percpu_store_entry`
still observed the pre-call **empty** global, so its `g_percpu[0] = entry` grew an
empty array to length **1**, and that one-element table is what got published.
Every `cpu_id >= 1` access then trapped.

It was neither an off-by-one nor a wrong MAX_CPUS: `MAX_CPUS` is 32 and the loop
really ran 32 times (`[PROBE] after push loop i=32 len=32`), while the sibling
function printed `store_entry sees len=0`.

## Fix

`src/os/kernel/smp/percpu.spl` — `percpu_init` now builds the **entire** table,
BSP entry included, in a local `var table: [PerCpu]`, and publishes it to
`g_percpu` with one assignment at the end. No callee reads `g_percpu` after this
function writes it. A comment in the function records the hazard.

Spec was NOT weakened; no assertion was changed. Only `percpu.spl` is modified.

## Verdicts (`bin/simple run`, per describe block)

| describe | before | after (JIT) | after (interpreter) |
|---|---|---|---|
| smp_init | 1 ex, 1 fail | 1 ex, 0 fail | 1 ex, 0 fail |
| smp_bringup_ap | 3 ex, 1 fail | 3 ex, 0 fail | 3 ex, 0 fail |
| firmware APIC registration | 4 ex, 4 fail | 4 ex, 0 fail | 4 ex, 0 fail |
| smp IPIs | 4 ex, 4 fail | 4 ex, 0 fail | 4 ex, 0 fail |
| preemption counter | 1 ex, 0 fail | 1 ex, 0 fail | 1 ex, 0 fail |
| IPI reason constants | 1 ex, 0 fail | 1 ex, 0 fail | 1 ex, 0 fail |

Total 14 examples: 10 failures -> 0 failures. JIT and interpreter agree.
No masked second defect was revealed — every previously-blocked assertion passes
on its first actual execution.

## Neighbouring specs (no regression)

| spec | result |
|---|---|
| test/01_unit/os/kernel/scheduler/green_carrier_spec.spl | 38 examples, 0 failures |
| test/01_unit/os/kernel/arch/riscv/hal_smp_spec.spl | 12 examples, 0 failures |
| test/unit/os/kernel/smp/smp_spec.spl (older copy) | 3 + 4 + 4 examples, 0 failures |

Lint: `bin/simple lint src/os/kernel/smp/percpu.spl` — 3 errors / 1 warning,
vs HEAD baseline 3 errors / 2 warnings. All pre-existing (COLL006 false positives
on numeric `i = i + 1` in while loops); no new finding introduced.

## Open engine defect to file

Global-write-not-visible-to-callee (above). Not fixed here — `src/compiler/**`
is out of this lane's scope. Any kernel module that writes a global and then
calls a helper reading it is silently miscompiled the same way; a repo-wide sweep
for that shape is warranted.
