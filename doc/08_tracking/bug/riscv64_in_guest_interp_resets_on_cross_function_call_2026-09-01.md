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

## 2026-09-01, next lane: the bad word DECODES, and it is not a field value

Two of the prior lane's framings are corrected here, both by direct reading of
the tree rather than by another boot.

### Correction 1 — the row-1/row-2 delta is NOT "MIR lowering ran"

The prior section proposed that the only difference between the green
interpreter row and the red build-and-run row is that row 2 runs
`MirLowering.lower_module` first. That is false. The two rows interpret
**different programs**:

* row 1 (`interpreter_hello_entry.spl:84-86`) is `fn main():` and two `print`s.
  **One function. No callee. No declared return type. No call.**
* row 2 (`buildrun_sanity_entry.spl:71-79`) is
  `fn add(a: i64, b: i64) -> i64` **plus** `fn main()` which CALLS `add`.

`interpret_hir_module` (`70.backend/backend/interpreter.spl:190-196`) reaches
`call_hir_function` for `main` by iterating `module.functions.values()` and
binding a **typed local** `val f: HirFunction` — the ANY-erasure cure that file
documents at length, and the path row 1 proves green. Row 2 additionally
resolves `add` through the callee-lookup path
(`ctx.fn_by_name` / `call_function_by_id`'s `ctx.module.functions[method_id]`),
which is a **dict `[]` read whose value is a struct**. So the bug title is
right and the discriminator is the CALL, not MIR lowering.

### Correction 2 — `0x3200000001` is a HeapHeader, not a corrupt pointer

The prior lane read the word as `TAG_HEAP | 0x3200000000` and concluded
"non-null, not a pointer". The tag arithmetic is right but the value is not a
mangled pointer at all. In the runtime that is ACTUALLY linked into this image,
`baremetal_runtime_core.inc.c:58-61`:

```c
typedef struct { uint32_t type; uint32_t size; } HeapHeader;   /* 8 bytes */
```

Little-endian, that struct read as one 64-bit word is `(size << 32) | type`.

```
0x00000032_00000001  ->  type = 1, size = 50
                         #define HEAP_STRING 1U      (same TU, line 38)
```

**The word at `HirFunction+32` is the header of a 50-byte `RuntimeString`.**
It is a valid, well-formed heap object header that merely happens to have
`TAG_HEAP` in its low bits, which is why the emitted clone's tag test accepted
it and dereferenced `size<<32` as an address. The clone's tag test is correct;
the DATA is not a field value at all.

### What that means, and the next question

If byte 32 of the object is where a neighbouring string BEGINS, then the object
`call_hir_function` was handed is not a 248-byte `HirFunction` — the `+32` load
walks off its end into the next bump allocation. The bump allocator aligns to
16 (`rv_size_align16`), and the one runtime struct in this TU that is **exactly
32 bytes** is `RuntimeArray` (`hdr` 8 + `len` 8 + `cap` 8 + `items` 8,
`baremetal_runtime_core.inc.c:71-76`).

So the leading hypothesis is now: **the value reaching `call_hir_function`'s
`fn_` parameter is a `RuntimeArray` handle, not a `HirFunction`** — and the
248-byte by-value COW clone of that parameter reads 248 bytes out of a 32-byte
object, hitting the next allocation's header at the first heap-tagged slot past
its end. The three fields BEFORE the fault (`name`, `type_params`, `params` at
+8/+16/+24) cloning "successfully" is consistent with this and is NOT evidence
the object is a HirFunction: +8/+16/+24 are `RuntimeArray.len`/`cap`/`items`,
and `len`/`cap` are small raw counts whose low bits are not `TAG_HEAP`, so the
clone skips them rather than validating them.

**Not claimed:** which call site supplies the wrong value — a dict `[]` read
returning an internal array (`d->keys`/`d->vals`), a miss returning the wrong
handle, or an argument-order/ABI mismatch that passes `args: [Value]` where
`fn_: HirFunction` belongs. All three produce a 32-byte array handle and are
separated by printing the RAW `hdr.type` of the `fn_` handle on entry to
`call_hir_function`, which is a strictly cheaper probe than the
before/after-MIR probe the prior section proposed (that probe tests a
discriminator now known to be the wrong one).

## ROOT CAUSE — `rt_unwrap_or_trap` never unwrapped (fix `b655e343cdb`)

The section above ended at three candidates and a probe. The probe was not
needed: the third candidate is right, and the tree proves it without a boot.

`examples/09_embedded/simple_os/arch/riscv64/boot/baremetal_runtime_core.inc.c`
defined, in full:

```c
RuntimeValue rt_unwrap_or_trap(RuntimeValue value)
{
    if (value == NIL_VALUE) { ...trap... }
    return value;                 /* <-- the Some-BOX, not its payload */
}
```

Its only test was `== NIL_VALUE`. Two independent fail-opens follow: a boxed
`Some(x)` is returned VERBATIM, so callers receive the 24-byte `RuntimeEnum`
wrapper where the payload belongs; and a boxed `None`/`Err` passes through
silently instead of trapping.

### The chain, end to end, with every measured number accounted for

1. The interpreter resolves a CALLEE through
   `resolve_function_by_name(name, ctx) -> HirFunction?`
   (`70.backend/backend/interpreter_calls.spl:137-153`) and then
   `cf_target_hit.unwrap()` (`:181`, and the sibling at
   `interpreter_expr.spl:311`).
2. `.unwrap()` returns the Some-box. `call_hir_function` (`:195`) therefore
   binds `fn_: HirFunction` to a 24-byte `RuntimeEnum` living in a 32-byte
   `rv_alloc` slot (the bump allocator aligns to 16).
3. Entry to `call_hir_function` makes the by-value COW copy of `fn_` —
   `rt_alloc(248)` at `807116ac`, the 31-field `HirFunction` — and walks the
   source's slots. `+8`/`+16`/`+24` are the wrapper's `enum_id|discriminant`,
   its `payload`, and zero padding; none of them faults, which is why the three
   heap fields "before" `return_type` appeared to clone fine. That was never
   evidence the object was a `HirFunction`.
4. `+32` is PAST the 32-byte slot: it reads the next bump allocation's
   `HeapHeader`, `0x0000003200000001` = `type=1` (`HEAP_STRING`), `size=50`.
5. That word has `TAG_HEAP` in its low bits, so the clone's tag test accepts it
   and dereferences `size << 32` as an address: `scause=0x5` load access fault,
   `stval=0x3200000000`, `sepc` in `call_hir_function+0x414`. Stack guard intact,
   `sp` 8 MB high — consistent, because nothing about this is a stack problem.

Row 1 stayed GREEN because `interpret_hir_module` reaches `call_hir_function`
only via `module.functions.values()` + a typed local (`interpreter.spl:190-196`)
and passes the `HirFunction` DIRECTLY. It never wraps an optional, and its
program has no callee at all.

### This was already fixed once, on the sibling architecture

`examples/09_embedded/simple_os/arch/common/boot/freestanding_value_registry_impl.h:149`
carries the correct implementation, and its comment describes this identical
failure in the same terms — "every `.unwrap()` fell through returning the
WRAPPER instead of the payload ... the first field load off it faults" — for the
x86_64 L5 VFS blocker
(`vfs_l5_fat32core_open_faults_on_new_file_write_2026-08-31.md`). That fix landed
in the COMMON header and the x86_64 lane. riscv64 carries its OWN duplicate
definition in its own boot TU, which shadows the sibling for this lane and was
never brought along. **A tree-wide grep for `rt_unwrap_or_trap` finds the good
sibling and looks green** — the duplicate-definition trap this boot directory
has now been bitten by four times.

Canonical semantics also exist at `src/runtime/runtime_native.c:12972` (hosted C)
and `src/runtime/simple_core/core_values.spl:142` (pure Simple). Both
discriminant forms are accepted by the fix, deliberately: simple-core builds
canonical Options with ORDINAL discriminants (Some=0, None=1) while native
lowering identifies Ok/Err by the stable 32-bit variant-name hashes, so a
hash-only fix would still return the wrapper for an ordinal-built Option.

`riscv32` has no `rt_unwrap_or_trap` at all (grep of
`examples/09_embedded/simple_os/arch/riscv32/`), so it carries no broken twin —
but it will need the symbol whenever its lane starts executing optionals.

### Guard

`scripts/check/check-rv64-unwrap-or-trap-unwraps.shs` — verified RED against
`b655e343cdb~1` and GREEN after. Deliberately NOT a source-shape ratchet like
its neighbour `check-rv64-rt-contains-has-dict-arm.shs`: a shape check cannot
distinguish a correct unwrap from one that reaches the `HEAP_ENUM` arm and still
returns the wrapper, which is this defect exactly. It extracts the real body,
host-compiles it against a `_Static_assert`-pinned transcription of the TU's
value layout, and asserts a Some-box yields its PAYLOAD. `--selftest` fatal,
6 fixtures, three of them must-FAIL (pre-fix body; a hash-only HALF-fix; an
uncompilable body). Wired in `.github/workflows/repo-hygiene.yml`.
