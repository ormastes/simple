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


---

# LOCALISED 2026-09-01 (fourth session) — it was never a "reset"

## Why nobody could see it: the guest had NO TRAP VECTOR

`crt0.S` set gp/sp, zeroed `.bss` and called `boot_entry` with **`stvec` never
written**. The tree's only `csrw stvec` lived inside the U-mode fs-exec path in
`baremetal_stubs.c`, which `rt_riscv_fs_exec_run()` fails closed on (returns
-13) and no lane reaches. So every S-mode exception vectored to whatever the
firmware left behind, printed nothing, and reached serial only as "the guest
resets and the entry re-enters from the top". Three sessions were spent reading
that silence; the machine was never resetting, it was faulting.

Fixed in `503f50f355c`: a real S-mode trap vector on a dedicated
`sscratch`-swapped stack (a blown kernel stack must not fault the reporter),
dumping `scause/sepc/stval/sp` as RAW HEX by a nibble loop — never
`rt_raw_i64_to_string`, which this image does not define. It PARKS; it never
returns and never resets. Plus a painted `.stack` guard band checked at the
single `rv_alloc` funnel, because `linker_riscv_common.ld` puts `.stack`
directly below `.bss/.data/.text` with no MMU, so a stack overflow takes no
fault at all and silently eats data and then code.

Both definitions are in `boot_entry.c`, the one rv64 boot TU with **no
duplicate twin**, so the stubs/`.inc.c` shadowing trap that cost two earlier
sessions cannot apply. Guarded by
`scripts/check/check-riscv64-boot-installs-trap-vector.shs` (RED against
`503f50f355c~1`, GREEN after; `--selftest` fatal, 5 fixtures).

## The measured trap frame

Full gate, real OpenSBI v1.4 `-bios fw_payload`, selftest OK (23 fixtures),
nonce `16b494361b6de5a7`. **Row 1 (interp) is GREEN.** Row 2:

```
[buildrun] phase=hir-ok
[buildrun] phase=mir-ok functions lowered
[buildrun] running the built program
[TRAP] S-mode exception, the guest is parking here
[TRAP]   scause=0x0000000000000005 sepc=0x0000000080711a70
[TRAP]   stval=0x0000003200000000 sp=0x0000000080f4d1a0
[TRAP]   _stack_bottom=0x000000008074d890 stack_guard=intact
[TRAP] parked
```

`scause=5` is a **load access fault**. `stack_guard=intact` and `sp` is 8 MB
above `_stack_bottom`, so **stack overflow is EXCLUDED** — and so is the
infinite-recursion theory that predicted it.

Verdict of record: `FAIL — 2 row(s) checked in-guest under real OpenSBI v1.4
firmware (nonce 16b494361b6de5a7), offender(s): build-and-run row`.
Serial: `build/os/riscv64_interp/run/buildrun-serial.log`.
Vector confirmed physically present in BOTH images with `nm`
(`0000000080200160 T rv64_boot_trap_vector`, 4-byte aligned) before the log was
trusted.

## Where sepc lands, disassembled

`sepc` is inside
`compiler__backend__backend__interpreter_calls__InterpreterBackendImpl_dot_call_hir_function`
at `+0x414` — the cross-function call itself, as predicted. The emitted code:

```
80711a1c:  ld    a0, 88(sp)        # a0 = the struct being copied
80711a20:  sd    a3, 0(a0)
80711a24:  ld    s10, 32(a0)       # s10 = field at byte offset 32
80711a28:  li    s9, 16
80711a44:  jalr  a3                # p = rt_alloc(16)
80711a48:  andi  a3, s10, 7        # tag bits
80711a4c:  xori  a2, a3, 1
80711a50:  seqz  a4, a2            # tag == TAG_HEAP ?
80711a54:  andi  a3, s10, -8       # pointer part
80711a58:  snez  a5, a3
80711a5c:  and   s1, a4, a5        # "looks like a heap ref"
80711a68:  bnez  a2, 80711a70
80711a6c:  mv    a4, a0
80711a70:  ld    a3, 0(a4)         # *** FAULT ***
```

This is the **value-semantics (COW) deep copy of a struct field**: allocate 16
bytes, then clone two words from the field IF its low three bits are
`TAG_HEAP`. `s10` was `0x0000003200000001` — tag 1, "pointer" `0x3200000000`,
which is nowhere near the kernel's `0x80…` address space. `stval` is exactly
that address.

## The lead, pinned by an ARITHMETIC fingerprint (not a guess)

The first draft of this section named `HirParam.default`. That was wrong, and
the allocation-size fingerprint settles it. Every COW clone in this function
allocates the exact byte size of the object it copies, so the ordered list of
`rt_alloc` sizes across `call_hir_function` is a layout fingerprint that can be
matched against candidate structs statically, with no boot:

| site | size | matches |
|---|---|---|
| `807116ac  li a0,248` | 248 = 31 slots | `HirFunction` — 31 fields (`hir_definitions.spl`). This is the by-value copy of the `fn_: HirFunction` parameter on entry. |
| `80711a28  li s9,16`  | 16 = 2 slots  | `HirType` — exactly 2 fields, `kind: HirTypeKind` and `span: Span` (`src/compiler/20.hir/hir_types.spl:541`). |
| `80711ba8  li a0,40`  | 40 = 5 slots  | (later clone, not on the faulting path) |

The faulting load reads byte offset **32** of the 248-byte `HirFunction` copy.
`HirFunction`'s 8-byte slots run 0 `symbol`, 8 `name`, 16 `type_params`,
24 `params`, **32 `return_type: HirType`** — and the clone that faults
allocates exactly 16 bytes, exactly `HirType`'s size. Both ends agree.

**So the bad word is `HirFunction.return_type`.** It holds `0x3200000001`:
`TAG_HEAP`, non-null, and pointing at `0x3200000000`, which is not in the
kernel's `0x80…` space. The three heap fields BEFORE it (`name`,
`type_params`, `params`) clone without faulting, so the corruption is specific
to this field, not general.

That lands in the same struct and the same defect family as one of the five
fixes already on this branch: `match_result_mir_type` dereferenced a **zeroed
`HirType`** bound by an if-val extraction from an absent optional. `HirType` is
non-optional in `HirFunction`, so a function with no declared return type has
to store *something* there — and in-guest that something reads as a valid heap
reference instead of failing. Same shape as all five earlier fixes.

## The discriminator the next session should use first

Row 1 also calls `main` through `call_hir_function`, and its `fn main():` also
declares no return type — yet row 1 is GREEN. The one thing row 2 does that
row 1 does not is run `MirLowering.lower_module(hir)` **before**
`interpret_hir_module(hir)`. Under Simple's value semantics that must not be
observable, but COW is precisely the machinery that is broken in this guest.

So the first question is not "what writes `return_type`" but **"does
`hir.functions[...].return_type` differ before and after MIR lowering
in-guest?"** One batched boot answers it: print the raw 64-bit word at
`return_type` for each function immediately after `phase=hir-ok` and again
immediately after `phase=mir-ok`. Print via a C helper exported from
`boot_entry.c` reusing the trap vector's nibble loop — RAW hex, never a
comparison result, and never an integer interpolated into Simple text
(`rt_raw_i64_to_string` does not exist in this image and calling it is itself a
null jump).

**Not claimed:** which side writes the bad word. The fingerprint pins WHICH
field faults; it does not say whether HIR lowering wrote it, MIR lowering
clobbered it through a COW alias, or the clone reads a correct field at a wrong
width. Those point at different halves of the tree and the probe above
separates them.
