# riscv64 in-guest: the guest RESETS while executing a cross-function call

- Status: **OPEN** — the current blocker for goal item 1 row 2.
- Date: 2026-09-01
- Lane: `scripts/check/check-simpleos-riscv64-interpreter-in-guest-opensbi.shs`
  row 2 (`buildrun`)
- Measured under real OpenSBI v1.4 `-bios fw_payload` (never `-kernel`, never
  `isa-debug-exit`), nonce 2b59d9831fd35815, gate selftest OK (23 fixtures).

## How the row got here (two blockers cleared today)

1. `E-MIR-TYPE-ZeroKind` — `match_result_mir_type` dereferenced a zeroed
   `HirType` bound by an if-val extraction from an ABSENT optional. Fixed;
   `phase=mir-ok functions lowered` now appears for the first time.
2. `function 'add' not found` — the baremetal `rt_contains` had no `HEAP_DICT`
   arm, so every `dict.has(k)` answered false in-guest and
   `resolve_function_by_name` fail-closed on `has_fn_index` before its linear
   scan. Fixed by delegating to `rt_dict_contains`.

## Symptom, measured

```
[buildrun] phase=hir-ok
[buildrun] phase=mir-ok functions lowered
[buildrun] running the built program
                                          <-- no further row output
[buildrun] SimpleOS riscv64 in-guest build-and-run sanity (OpenSBI fw_payload)
[buildrun] serial up, building then running a Simple program     <-- REBOOTED
```

The `function 'add' not found` failure is GONE — callee resolution now
succeeds. The guest instead RESETS while executing the program and re-enters
the entry from the top, looping. No trap frame is printed before the reset.

## What is NOT yet known

Whether the fault is in the call itself (`call_hir_function` on a resolved
`HirFunction`), in the argument marshalling, or in something the callee body
touches. Nothing here is measured beyond "the row reaches execution and the
machine resets", and that is deliberately all this record claims.

Next step, in the style that worked twice today: batch several probes into ONE
boot rather than guessing — the boot cycle is ~25 minutes. Print RAW values,
never a comparison result, and never interpolate an integer into text (that
emits `rt_raw_i64_to_string`, which this runtime does not provide, and the lane
tolerates unresolved symbols, so it becomes a NULL-GOT fault rather than a link
error). Verify any probe is physically in `kernel.elf` before trusting a silent
result.

## Re-confirmed on the probe-free tree

The measurement above (nonce 2b59d9831fd35815) was taken with the temporary
row-2 probes still in the image. After removing all of them the row was rebooted
from the cleaned tree — nonce **804651e7362b19ea**, real OpenSBI v1.4
`-bios fw_payload`, gate selftest OK (23 fixtures) — and behaves identically:

```
[buildrun] phase=hir-ok
[buildrun] phase=mir-ok functions lowered
[buildrun] running the built program
                                          <-- resets, entry re-enters from the top
```

So the reset is a property of the tree being reported, not of the probes.
