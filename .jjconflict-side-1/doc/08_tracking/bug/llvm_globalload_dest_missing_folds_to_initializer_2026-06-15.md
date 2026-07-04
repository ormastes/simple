# Bug: LLVM backend — module-global variable reads fold to their initializer (GlobalLoad missing from `MirInst::dest()`)

- **ID:** llvm_globalload_dest_missing_folds_to_initializer_2026-06-15
- **Severity:** P1 (silent miscompilation; any module-level `var`/`val` read inside a function returns the static initializer, not the current runtime value)
- **Backend:** LLVM (target-independent — reproduced on `x86_64-unknown-linux-gnu` and `riscv64-unknown-none`)
- **Status:** FIXED (see Fix)

## Symptom

The riscv64 SimpleOS web-server kernel boots through service init, reaches every
storage/network marker, then on `[os_main] Probing root filesystem (freestanding)...`
faults with a load from address `0x8` and the S-mode trap handler silently restarts
boot (~4263 times). The gate (`scripts/qemu/qemu_rv64_http_test.shs --with-storage`)
never reaches HTTP bind.

QEMU trap log (`-d int,guest_errors`):
```
riscv_cpu_do_interrupt: cause:0x5 (fault_load) epc:0x8020ea7a tval:0x8
Invalid read at addr 0x8, size 8, region '(null)', reason: rejected
```
`addr2line 0x8020ea7a` → `boot_nvme_production_handoff_ready`. fault count (4262)
is 1:1 with `Probing root filesystem` occurrences — the fault drives the loop.

## Minimal repro (target-independent)

`/tmp/scalar.spl` (scalar global — exit 0 but prints WRONG answer):
```simple
var _g: i64 = 0
fn set_g():
    _g = 5
fn ready() -> bool:
    _g > 0          # returns false even though set_g() set _g = 5
fn main():
    set_g()
    if ready():
        print("READY")
    else:
        print("NOT READY")   # <-- this branch taken (BUG)
```
`var _g: [i64] = []` + `_g.len() > 0` SIGSEGVs (exit 139): `.len()` reads offset
8 of the folded-0 array pointer (`ld a1, 8(zero)` on RV64; `cmpq $0x0, 0x8` on x86).

## Root cause

`MirInst::dest()` (`compiler/src/mir/inst_helpers.rs`) lists 104 of the 105
dest-bearing MIR variants; **`GlobalLoad` is the only one missing** — it falls
into the `_ => None` catch-all.

The LLVM backend (`codegen/llvm/functions.rs`) keeps every VReg in a stack alloca
for cross-block SSA correctness, refreshes `vreg_map` from allocas at each block
boundary (and `vreg_map.clear()` after each instruction), and stores an
instruction's result back to its alloca **only when `inst.dest()` is `Some`**
(line ~653). Because `GlobalLoad`'s `dest()` is `None`:
- The loaded value (`%gload = load i64, ptr @___g`) is inserted into `vreg_map`
  but never stored to the VReg's alloca, then `vreg_map.clear()` discards it.
- The liveness pass (line ~597) also fails to record the def, so the VReg is
  treated as live-in and reloaded stale (initializer) from its alloca.

Emitted LLVM IR for `ready()` shows the asymmetry directly:
```llvm
%gload = load i64, ptr @___g        ; computed...
store i64 0, ptr %v1                 ; VReg(1) = 0
%v01 = load i64, ptr %v0            ; ...but VReg(0) read from alloca (=0), not %gload
%gt = icmp sgt i64 %v01, %v12       ; 0 > 0  → false
```
Writes are fine: `GlobalStore` (`store i64 %v01, ptr @___g`) works, so the symbol
resolves; only the *read* of a global was dropped.

This is a PRE-EXISTING LLVM-codegen bug, NOT caused by the recent linker.rs
`--defsym` bridges or the new `freestanding_runtime.c` rt_* functions. It only
surfaced now because this is the first from-source LLVM kernel boot (prior gate
runs used `--allow-prebuilt-artifact`). Matches the known family
`module_level_text_const_empty_in_jit` / `jit_string_method_on_var_receiver_folds`.

## Fix

`compiler/src/mir/inst_helpers.rs`, in `dest()`: add `GlobalLoad` to the
`Some(*dest)` arm. One line. Fixes both the store-back AND the liveness pass
consistently. Requires a seed rebuild (`cargo build --release --features llvm`).
`dest()` is a shared MIR helper; the change is strictly "more correct" (GlobalLoad
genuinely defines its dest), and may also benefit cranelift/interpreter paths.
