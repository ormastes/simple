# riscv64 in-guest: `hir.functions.values()` yields EMPTY while `.len()` reports non-empty

- Status: **RESOLVED 2026-09-01.** Row 1 is GREEN in-guest under real OpenSBI v1.4 `-bios fw_payload`. See ROOT CAUSE below.
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


---

# ROOT CAUSE AND FIX (2026-09-01, third session)

## The answer

`baremetal_stubs.c`, **not** `baremetal_runtime_core.inc.c`, is the translation
unit whose `rt_index_get` / `rt_index_set` / `rt_len` WIN the link. Both TUs are
linked into the kernel; the DUPLICATED names resolve to `baremetal_stubs.c`.

`baremetal_stubs.c`'s `rt_index_set` was, in full:

```c
RuntimeValue rt_index_set(RuntimeValue value, RuntimeValue index, RuntimeValue item)
{
    if (!IS_INT(index)) return 0;  /* <- every dict write died here */
    return rt_array_set(value, (RuntimeValue)DECODE_INT(index), item);
}
```

`d[k] = v` lowers to `rt_index_set`. Every write into a dict with a non-int key
was discarded silently, with no trap and no error. That is every dict in the
frontend: `ParserModule.functions : Dict<text, ParserFunction>` and
`HirModule.functions : Dict<SymbolId, HirFunction>`.

The previous session added exactly this dict arm — to the `.inc.c` copy, the one
that LOSES the link. That is precisely why "it did not move row 1". The tree's
own comment above `rt_index_get` in `baremetal_stubs.c` already recorded this
trap ("this TU, not baremetal_runtime_core.inc.c, is the definition that
actually WINS the link ... Fixing only the .inc.c copy changed nothing
in-guest") and it was not applied to the sibling function.

## The mandated `.len()`-vs-`.values()` test, and its answer

Run first, as the doc demanded. Three probe boots under real OpenSBI fw_payload:

| measurement | result |
|---|---|
| `hir.functions.len()` tick-loop | **0 ticks** |
| `hir.functions.values()` tick-loop | **0 ticks** |
| `parsed.function_order` (an ARRAY) tick-loop | **1 tick** |
| `parsed.functions` (a DICT) tick-loop | **0 ticks** |
| `rt_dict_values` entered | 7x, `len=0` each |
| `rt_index_set` entered (`.inc.c` copy, instrumented) | **0** |
| `simpleos_dict_store` entered | **0** |
| `rt_dict_new` entered | >=120 |

So `.len()` and `.values()` **AGREE** — the dict really is empty. The doc's
`.len()`-is-lying fork is **excluded**, and so is its "chase HIR lowering" fork:
the dict is already empty **at the parser**, one whole phase earlier, while the
array beside it in the same struct holds its entry. Dicts are created fine; only
writes vanish.

`nm kernel.elf` then closed it: `rt_index_set` resolved into
`baremetal_stubs.c`'s address range, and `rt_dict_set` / `simpleos_dict_store`
were **absent from the linked image entirely** — the latter because its only
callers lived in the `.inc.c` copies that lose.

## Secondary defect, NOT fixed here (filed separately below)

The `if hir.functions.len() == 0:` guard did not fire even though the tick-loop
proved `len()` is 0: in the same boot, `while pi < nfn` ran 0 times while both
`nfn == 0` and `hir.functions.len() == 0` evaluated **false**. A `<` comparison
and an `== 0` comparison over the same value disagree in the freestanding
riscv64 guest. Neither `rt_len`, `rt_array_len` nor `rt_dict_len` was entered
even once across a whole boot, so `.len()` is not routed through any of them.
Once dict writes land, row 1 no longer exercises this, so it is left as its own
record rather than expanded into this change. It is a real fail-open: the guard
that exists to catch an empty module cannot fire.

## Fix

Dict arms added to `rt_index_set`, `rt_index_get` and `rt_len` in
`examples/09_embedded/simple_os/arch/riscv64/boot/baremetal_stubs.c`, routed to
the existing `simpleos_dict_store` / `simpleos_dict_lookup` /
`simpleos_dict_count` in `baremetal_runtime_core.inc.c` (declared, not
re-implemented — declaring them is also what stops `--gc-sections` from
dropping `simpleos_dict_store`, which had no surviving caller).

## Evidence

Serial, real OpenSBI v1.4 `fw_payload`, positively-asserted embed, no `-kernel`,
no `isa-debug-exit`:

```
[interp] hir ready, invoking InterpreterBackendImpl.interpret_hir_module
HELLO_INTERP_SIMPLEOS_RISCV64_OK nonce=probe1788243472
HELLO_INTERP_SIMPLEOS_RISCV64 second line proves the interpreter kept running
[interp] interpreter returned Ok
[interp] interpreter row exited rc=0
```

## Guard

`scripts/check/check-freestanding-dict-arms-in-every-definition.shs` — per
DEFINITION, not per tree, because a tree-wide grep is exactly the check that
would have passed throughout this failure. Verified RED against this fix's
parent (`e5273bcb2f0`: `FAIL — 6 definition(s) checked, missing a HEAP_DICT arm:
baremetal_stubs.c:rt_index_get baremetal_stubs.c:rt_index_set
baremetal_stubs.c:rt_len`) and GREEN after. `--selftest` is fatal, 4 fixtures,
including a must-FAIL fixture replaying the incident's exact shape (two TUs,
arm only in the non-winning one) and a decoy fixture proving an unrelated
`HEAP_DICT` mention elsewhere in the file does not satisfy the check.

## Meta-defect, recorded not fixed

The duplicate-definition arrangement itself is the hazard: two TUs define the
same runtime entry points, the link silently picks one, and a fix to the other
looks correct in source review and is inert at runtime. It has now cost two
sessions on this one function. Deduplicating the boot TUs is a separate change.
