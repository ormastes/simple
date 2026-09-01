# riscv64 in-guest: `Dict.values()` yields EMPTY on an ANY-erased receiver, and never reaches `rt_dict_values`

- Status: OPEN — this is the single remaining blocker for goal row 1
- Date: 2026-09-01
- Lane: `scripts/check/check-simpleos-riscv64-interpreter-in-guest-opensbi.shs`
- Class: same family as
  `riscv64_erased_receiver_routes_class_method_to_rt_find_2026-08-31.md`
  (an ANY-erased receiver's method call landing somewhere other than the
  entry point the method registry names for that type).

## Symptom

Row 1 fails in-guest, under real OpenSBI v1.4 `-bios fw_payload`, with:

```
[interp] hir ready, invoking InterpreterBackendImpl.interpret_hir_module
[interp] FAIL interpreter error: module has no main function
```

HIR lowering succeeds. The same sequence on the HOST reports
`FUNCTION_NAMES=[main]` and interprets fine, so this is freestanding-only.

## What was MEASURED, not inferred

An in-guest probe was added to `interpreter_hello_entry.spl` (temporary, since
removed) directly after the HIR is built, plus a temporary C diagnostic inside
`rt_dict_values`. Booted under real OpenSBI fw_payload with a positively
asserted embed. Transcript:

```
[interp] hir ready, invoking InterpreterBackendImpl.interpret_hir_module
[probe] values-empty=yes
[probe] loop-done
[probe] eq-literal=yes
[probe] eq-built=yes
[interp] FAIL interpreter error: module has no main function
```

and, from the C diagnostic inside `rt_dict_values`, **zero lines** — it was
never entered at all.

Three candidate causes were on the table. Two are now EXCLUDED by measurement:

- **The text compare is innocent.** `"main" == "main"` and
  `("ma" + "in") == "main"` both answer yes in the same boot. The string-eq
  primitive works.
- **The function names are irrelevant.** No per-function line was printed at
  all, so nothing was ever compared. A name-bytes defect (the
  `rt_string_bytes` family) cannot be the cause of an empty iteration.
- **What remains:** `hir.functions.values()` returns an EMPTY array.

## The contradiction that localises it

In the same boot, over the same object:

| route | answer |
|---|---|
| `hir.functions.len()` | **> 0** (the `== 0` guard above does not fire) |
| `hir.functions.values()` | **empty** |

Two routes disagree about one dict. And the C diagnostic proves `.values()`
never reached `rt_dict_values`, which IS defined and IS present in the linked
ELF. So the call is being dispatched somewhere else, and that somewhere yields
an empty array rather than failing.

`.len()` answering correctly is consistent with it landing on `rt_array_len`
(which IS referenced by the guest objects, while `rt_len` is not present in the
final ELF): `RuntimeDict` carries `len` immediately after the header, exactly
like `RuntimeArray`, so an array-shaped read of a dict handle returns the real
count. That is a wrong route giving a right answer, which is why it masked the
defect for so long.

## Why the obvious fix was NOT the cause

`rt_dict_set` was found REFERENCED by the generated guest objects
(`nm -u mod_*.o`) and defined by NO boot TU, with the lane's unresolved-symbol
bridge supplying a silent stub. That looked like a complete explanation and was
fixed (see `rt_dict_set` in `baremetal_runtime_core.inc.c`, plus dict arms added
to `rt_index_get` / `rt_index_set` / `rt_len`, pinned by
`scripts/check/check-freestanding-dict-write-path.shs`).

**It did not move row 1.** The row fails identically after the fix. The fix is
still correct and is kept — `rt_index_set` genuinely discarded every dict
subscript write with a non-int key — but it is NOT this defect's cause, and the
commit that landed it overstated the causal claim.

## Next step

Identify the entry point `.values()` on an ANY-erased `Dict` receiver actually
emits in the freestanding riscv64 lane, and why it returns empty instead of
failing. Note that 341 `rt_*` symbols referenced by the guest objects have no
definition in any boot TU and receive silent stubs; a stub returning an empty
array would produce exactly this signature. Do NOT rely on `objdump` symbol
grep for the call site — it has already reported zero call sites for functions
called seven times on this lane (inline literal pool).

## Evidence paths

- Serial: `build/os/riscv64_interp/run/probe-serial.log`,
  `build/os/riscv64_interp/run/probe2-serial.log`
- Gate verdict of record (both rows, real firmware):
  `FAIL — 2 row(s) checked in-guest under real OpenSBI v1.4 firmware`
