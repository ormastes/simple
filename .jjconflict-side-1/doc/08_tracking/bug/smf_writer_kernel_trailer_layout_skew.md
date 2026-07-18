# SMF writer/kernel trailer layout skew: toolchain cannot emit a kernel-recognized role-2 library

**Found by** Lane H8 (SMF dynamic-load in-guest gate), pinned by the last test
in `test/01_unit/os/kernel/loader/smf_dyload_spec.spl` ("documents the
writer/kernel trailer skew").

## Symptom

No compiler-emitted `.smf` can be recognized by the kernel loader as a role-2
(library) envelope. The kernel's strict role-2 library gate
(`loader_dynopen_smf_library_bytes_for_arch`) rejects all toolchain output.
Toolchain output is *tolerated* as an executable envelope only because the
kernel accepts `role == 0` (unspecified) as executable.

## Root cause: two disagreeing 128-byte trailer layouts

The kernel reader and the compiler writer place different fields at the same
byte offsets in the 128-byte EOF trailer.

**Kernel reader** — `src/os/kernel/loader/smf.spl`:
```
SMF_ROLE_OFFSET = 60   # 0=unspecified, 1=executable, 2=library
SMF_ARCH_OFFSET = 61   # 0=unspec, 1=x86_64, 2=x86, 3=arm64, 4=arm32, 5=rv64, 6=rv32
SMF_ABI_OFFSET  = 62   # 0=unspecified, 1=simpleos
```

**Compiler writer** — `src/compiler/70.backend/linker/smf_header.spl` (128-byte
header written as trailer): field groups Identification(8) + Flags(20) +
Symbols(16) + Execution(16) = 60, so **`module_hash` starts at byte 60**
(default value 0), and **`arch` is written at byte 7** of the Identification
group with a *different* arch enum (writer `x86_64 = 0` vs kernel `x86_64 = 1`).

Consequences:
- Byte 60 (kernel: role) = writer `module_hash` low byte = 0 → every toolchain
  module reads as `role = 0` (unspecified), never 1 (executable) or 2 (library).
- Byte 61 (kernel: arch) = writer `module_hash` byte = 0 → arch reads as
  unspecified regardless of the real target.
- Writer's real arch byte (offset 7) uses an incompatible enum the kernel never
  reads.

## Fix

Make the writer emit the kernel's trailer contract: write `role` at byte 60,
`arch` at byte 61 (kernel enum: x86_64=1, x86=2, arm64=3, arm32=4, rv64=5,
rv32=6), `abi` at byte 62 (1=simpleos). Set `role = 2` when emitting a shared
library, `role = 1` for an executable. Keep `module_hash` clear of bytes 60-62
(shift it into the Reserved(40) tail, or shrink it). Add a shared constant
module so writer and kernel reference the SAME offset/enum definitions instead
of two hand-maintained copies — this skew is exactly what a shared header
prevents.

## Verification

The gate spec's final example pins current (broken) behavior: toolchain SMF is
accepted as an executable envelope but rejected (-8) at the role-2 library gate.
When the writer is fixed, that example flips to *accepted* as a role-2 library —
update the spec to assert the fixed contract at that point.

## Test-harness note (separate, known bug)

The gate's real-toolchain-writer round-trip runs cross-process under
`SIMPLE_EXECUTION_MODE=interpret`, not default JIT: under seed JIT,
`text.bytes()` written via `rt_file_write_bytes` corrupts to pointer garbage and
`as`-cast struct-field assignments mangle (`0x400000 as u64` → 2^35;
`416 as u32` → 0). Same BoxInt-mangle family as
`jit_hex_to_u8_array_byte_corruption_2026-06-30.md`. Interpret mode is correct;
fix belongs in the seed JIT (gated on the #99 toolchain redeploy).
