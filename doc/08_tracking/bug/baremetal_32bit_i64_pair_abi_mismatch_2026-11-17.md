# 32-bit native backend: i64 args packed without ilp32 alignment; bm_rt.spl assumes i64 handles (2026-11-17)

- id: `baremetal_32bit_i64_pair_abi_mismatch_2026_11_17`
- severity: P2 (affects every 32-bit freestanding lane: riscv32, i686, arm32)
- status: verification-pending (runtime workaround landed; compiler-side alignment still open)

## Repro
`native-build freestanding_hello/main.spl --target riscv32-unknown-none` linked with `bm_rt.spl`
(all params `i64`), booted via OpenSBI fw_payload: `hello from ...` then NUL padding,
`panic("boom")` prints garbage and does not halt. `llvm-objdump -d -r main.o`:

    rt_println_str(ptr,len):  a0=ptr  a1=0x1c a2=0     ; len i64 packed in a1:a2
    rt_panic(ptr,len):        a0=ptr  a1=len_lo a2=len_hi
    rt_string_len -> a0:a1 (i64);  rt_strcat_tagged(a,b): a0,a1 (one reg each)

## Root cause
1. Call sites pass pointers/text handles as ONE 32-bit register and an i64 argument in the next
   two registers WITHOUT the even-register alignment the ilp32 psABI requires (len in a1:a2, not a2:a3).
2. `bm_rt.spl` declares every runtime param `i64`, so the callee reads `ptr` as a0:a1 (high word =
   the length) and `len` as a2:a3 (garbage) -> NUL-padded text, wrong panic text, and the panic never
   reaches `bm_halt` cleanly.

## Fix / plan
- Done (this PR): `bm_rt32.spl` declares the widths the backend really emits (`i32` handles, `len`
  as `i32 + len_hi`), plus `crt0_riscv32.S` with 32-bit args. i64 only in `rt_raw_i64_to_string`
  (MIN prints correctly, no compiler-rt helper needed). Pinned by
  `check-baremetal-efi-boot.shs --arch riscv32` (exact transcript, was failing before).
- Open (compiler): align i64 args to even register pairs on ilp32/ARM AAPCS (and make the runtime
  extern table state real widths) so a single `bm_rt.spl` can serve all arches. i686 (cdecl: stack
  words) and arm32 (AAPCS: even r-pair) lanes must reuse `bm_rt32.spl` or hit the same defect;
  per-arch crt0 must use 32-bit arguments.
- Similar-pattern tests: the transcript includes i64 0, -7, MAX, MIN and a text concat chain.
