# Bug: `bin/simple check` superlinear blowup with multiple `me` methods on array-field structs

**Filed:** 2026-06-29  
**Status:** Open  
**Affects:** `bin/simple check` (type-checker pass only — interpreter/run unaffected)

## Symptom

`bin/simple check` hangs indefinitely (no output, no error) when a file contains a
struct with ≥3 array (`[i64]`) fields and ≥3 `me` methods in the same `impl` block,
**or** when a file contains two structs with array fields where one struct has multiple
free functions performing chained array-index lookups.

`bin/simple run` is unaffected: the same code runs correctly at interpreter speed.

**Observed non-determinism (same file, same binary md5, no parallel rebuild):** the
failure mode varies across runs — sometimes a fast `rc=255` with zero output (a crash),
sometimes a `rc=124` timeout (a hang), and occasionally `rc=0 All checks passed`. This
crash/hang/pass variance points to memory corruption or an unbounded/ordering-dependent
loop in the check-only pass, not a clean deterministic rejection. A control file
(`examples/09_embedded/rv64_os_boot/main.spl`) checks `rc=0` deterministically, so the
trigger is the array-field-struct + multiple-`me`-method shape, not the environment.

## Minimal repro (hangs check, run is fine)

```simple
val PHASE_DONE: i64 = 4

struct Handle:
    index: i64
    generation: i64

struct Pool:
    gens: [i64]
    used: [i64]
    slot_phase: [i64]
    capacity: i64

impl Pool:
    me acquire() -> Handle:
        var i: i64 = 0
        while i < me.capacity:
            if me.used[i] == 0:
                me.used[i] = 1
                return Handle(index: i, generation: me.gens[i])
            i = i + 1
        Handle(index: -1, generation: -1)

    me step(h: Handle) -> i64:
        if h.index < 0 or h.index >= me.capacity:
            return -1
        if me.gens[h.index] != h.generation or me.used[h.index] == 0:
            return -1
        if me.slot_phase[h.index] < PHASE_DONE:
            me.slot_phase[h.index] = me.slot_phase[h.index] + 1
        me.slot_phase[h.index]

fn main():
    print "ok"
```

`bin/simple check repro.spl` → hangs (killed after 30+ s)  
`bin/simple run repro.spl` → prints `ok`, EXIT:0

## Bisection results

| Configuration | check result |
|---|---|
| 3 array fields, 1 `me` method | ✓ passes |
| 3 array fields, 2 `me` methods (step + release) | ✓ passes |
| 3 array fields, 3 `me` methods (acquire + step + release) | ✗ hangs |
| 3 array fields, 2 `me` methods + chained-index free fn in same file | ✗ hangs |
| 5 array fields, 2 `me` methods | ✗ hangs |

The blowup appears when `(num_array_fields × num_me_methods)` exceeds ~6, or when
compound conditions reading multiple array fields at the same index appear in multiple
functions. The type-checker creates a constraint graph whose size grows superlinearly
with these combinations.

## Workarounds

1. **Split large `impl` blocks into smaller files** — the check blowup is per-module.
2. **Reduce `me` methods** — move operations to free functions that take and return
   the struct (functional style). Confirmed to work for simple mutations.
3. **Avoid repeated compound conditions** — if `pool.gens[idx] != g or pool.used[idx] == 0`
   appears in multiple functions referencing the same struct, extract to one helper.

## Affected files

- `examples/09_embedded/simpleos_nvme_fw/main.spl` (impl Ftl with 4 me methods)
- `examples/09_embedded/simpleos_nvme_fw/pool_demo.spl` (impl TaskPool with 4 me methods)

Both files are split into two modules (rather than one) specifically to keep each
`impl` block small enough that the bug is not triggered — but with 4 `me` methods
each, both still hit the threshold.

## Root cause hypothesis

The type-checker appears to enumerate constraint combinations for array-field
accesses per function per struct, leading to O(n! / k!) growth where n = total
array accesses and k = method count. The run path (interpreter) does not perform
this inference pass, so it is unaffected.
