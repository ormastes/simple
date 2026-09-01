# riscv64 in-guest: `hir.functions.values()` yields EMPTY while `.len()` reports non-empty

- Status: OPEN — single remaining blocker for goal row 1. **RESOLVED to reading (b) by measurement: the dict is real and EMPTY; no write ever reaches it.**
- Date: 2026-09-01
- Lane: `scripts/check/check-simpleos-riscv64-interpreter-in-guest-opensbi.shs`
- Class: a freestanding-only disagreement between two read routes over one
  `Dict<SymbolId, HirFunction>`. NOTE the receiver here is STATICALLY typed
  (`hir: HirModule`, `functions: Dict<SymbolId, HirFunction>`), so this is the
  typed-Dict lowering path, NOT ANY erasure — an earlier draft of this doc said
  ANY erasure and was wrong. Related in spirit, but not the same mechanism, as
  `riscv64_erased_receiver_routes_class_method_to_rt_find_2026-08-31.md`.

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

and, from a temporary C diagnostic inside `rt_dict_values`, **zero lines**.

**Read that last fact carefully — it is weaker than it looks, and an earlier
draft of this doc over-read it.** The diagnostic printed only on the `!d`
branch, i.e. only when the handle was NOT a valid `HEAP_DICT`. Its silence is
therefore consistent with EITHER of:

  (a) `rt_dict_values` was never called at all, or
  (b) `rt_dict_values` WAS called with a perfectly valid `HEAP_DICT` whose
      `len` is 0 — i.e. the dict is genuinely EMPTY.

That ambiguity has since been RESOLVED by a second boot carrying unconditional
markers. Result:

```
      6 [DIAG] rt_dict_values entered
      6 [DIAG] rt_dict_values dict is EMPTY
```

and **zero** `[DIAG] simpleos_dict_store entered` lines.

So reading **(b)** is correct, and it is now established rather than inferred:

- `rt_dict_values` IS called (6 times) and the handle IS a valid `HEAP_DICT`.
  The `.values()` call is correctly routed. It is NOT misrouted.
- The dict's `len` is 0 every time — it is genuinely EMPTY.
- `simpleos_dict_store` — the single funnel through which BOTH `rt_dict_set`
  and the `rt_index_set` dict arm write — is **never entered even once**.

Therefore: **no insertion into `hir.functions` ever reaches the dict, and it
does not travel through `rt_dict_set` or `rt_index_set` either.** The write is
emitted as some third entry point, which is one of the 341 `rt_*` symbols the
guest objects reference with no definition in any boot TU and which the lane's
bridge answers with a silent stub.

Three candidate causes were on the table. Two are now EXCLUDED by measurement:

- **The text compare is innocent.** `"main" == "main"` and
  `("ma" + "in") == "main"` both answer yes in the same boot. The string-eq
  primitive works.
- **The function names are irrelevant.** No per-function line was printed at
  all, so nothing was ever compared. A name-bytes defect (the
  `rt_string_bytes` family) cannot be the cause of an empty iteration.
- **What remains, now positively established:** the dict really is EMPTY, and
  the write path never reaches it through any route this runtime defines.

## The contradiction that localises it

In the same boot, over the same object:

| route | answer |
|---|---|
| `hir.functions.len()` | **> 0** (the `== 0` guard above does not fire) |
| `hir.functions.values()` | **empty** |

Two routes disagree about one dict, and that disagreement is the core puzzle:
under reading (b) above the dict is empty, in which case `.len()` reporting
non-empty is itself the defect and `.values()` is telling the truth. Under
reading (a) the dict is populated and `.values()` is misrouted. **These point
at opposite halves of the runtime, so resolving (a)-vs-(b) is the mandatory
first step and no fix should be attempted before it.**

Note that neither `rt_dict_len` nor `rt_len` appears in the final linked ELF,
while `rt_array_len` IS referenced by the guest objects — so `.len()` is not
reaching either of the dict-aware length entry points.

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

(a)-vs-(b) is settled — see above. The one remaining question is:

**Which entry point does HIR lowering's insertion into
`Dict<SymbolId, HirFunction>` actually emit on this lane?** It is provably
neither `rt_dict_set` nor `rt_index_set` (both funnel through
`simpleos_dict_store`, which never runs). The referenced-minus-defined symbol
diff was searched for dict/map/insert/put/store/table-shaped names and turned
up NO other candidate, which makes a third runtime entry point unlikely.

**That points somewhere more interesting, and the next session should test it
first: `.len()` is the component that is lying, and the dict was empty all
along.** The chain is forced by the evidence:

- The dict is measured EMPTY at `.values()` time (6/6 boots, valid HEAP_DICT).
- No write ever reaches it through any defined route.
- Yet the `if hir.functions.len() == 0` guard in `interpreter_hello_entry.spl`
  does NOT fire, so `.len()` reports non-zero **on a dict that is empty**.

If `.len()` is simply wrong here, then nothing was ever dropped at the runtime
level — **HIR lowering produced a module with no functions in-guest**, the
`len() == 0` guard that exists precisely to catch that was defeated by a broken
`.len()`, and `interpret_hir_module` then correctly reported no `main`. The
runtime dict work in this lane would then be a real but SEPARATE fix, and the
actual row-1 blocker would be upstream in lowering.

Test to run first (one ~6-minute cycle): print `hir.functions.len()` as a
repeated-marker count in the guest entry alongside the `values-empty` line, and
put an unconditional marker in whatever `.len()` resolves to. If `.len()` and
`.values()` disagree on a dict the runtime says is empty, chase `.len()`; if
they agree, chase lowering. Do NOT resume patching dict write paths until this
is answered — two sessions have now been spent on the write side.

`.values()` lowers with `DispatchMode::Dynamic`
(`src/compiler_rust/compiler/src/hir/lower/expr/mod.rs:1681`), so the emitted
entry point is not necessarily the `rt_dict_values` that `method_registry/
builtins.rs:170` names for a statically-typed Dict receiver.

Fast cycle (measured): `native-build` of the interp entry alone is ~54s warm;
rebuilding the OpenSBI fw_payload and booting is ~5 min. There is no need to
run the full gate until a candidate fix is in hand. Note that 341 `rt_*` symbols referenced by the guest objects have no
definition in any boot TU and receive silent stubs; a stub returning an empty
array would produce exactly this signature. Do NOT rely on `objdump` symbol
grep for the call site — it has already reported zero call sites for functions
called seven times on this lane (inline literal pool).

## Evidence paths

- Serial: `build/os/riscv64_interp/run/probe-serial.log`,
  `build/os/riscv64_interp/run/probe2-serial.log`
- Gate verdict of record (both rows, real firmware):
  `FAIL — 2 row(s) checked in-guest under real OpenSBI v1.4 firmware`
