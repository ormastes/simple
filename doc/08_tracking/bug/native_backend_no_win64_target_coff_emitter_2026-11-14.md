# Pure-Simple native backend has no Windows x64 target: no Win64 ABI isel, no COFF emitter

Date: 2026-11-14
Status: open (design gap, found by lane xraywin; blocks XRay Stage 3 real run)

## Finding
`--backend=native --xray` on x86_64 Windows cannot be reached by mirroring the ELF path:

- `CodegenTarget` (`src/compiler/70.backend/backend/backend_types.spl:82`) has no Windows
  member; `compile_native` (`backend/native/mod.spl:43`) sends every non-ELF/Mach-O target to
  `compile_native_stub` (a 1-byte ELF `ret`).
- `isel_x86_64.spl` uses the single SysV table `X86_ARG_REGS` (rdi, rsi, ...) at
  lines 16/262/270/1199, with no Win64 convention (rcx, rdx, r8, r9, 32-byte shadow space,
  different callee-saved set). Native code for a Windows DLL would mis-pass arguments.
- No COFF object writer exists in the native backend. `backend/linker/coff/*` only PARSES
  objects (`coff_parse_object`) and writes PE images (`pe_image_writer.spl`); `native_elf.spl` /
  `elf_writer*.spl` have no COFF twin (sections, ADDR32NB/REL32 relocs, `.pdata`/`.xdata`).

So step 1 (COFF sled emission) is a new backend target (Win64 ABI lowering + COFF writer +
unwind tables), not a mirror of `emit_elf_x86_64_xray`. Route admission (step 2) must not
land before it, or `--xray` would admit a target whose code is ABI-wrong.

## Probe (step 3 blocker check) — NOT a blocker
Seed-tip `/c/dev/wt/seed-tip/simple.exe run` on a llvm-mingw `t.dll` exporting `probe_add`:
`rt_host_dynlib_open(path, 2)` -> non-zero handle, `rt_host_dynlib_symbol(h, "probe_add")` ->
non-zero address. Dynload works on Windows; the Linux `rt_host_dynlib_open` bug does not
reproduce. The `/proc/self/maps` binding in `xray_native_module_v1.spl` still needs a PE twin.

## Suggested split
1. Win64 CodegenTarget + ABI isel (arg regs, shadow space, callee-saved) with an off-identity gate.
2. COFF object writer (+ `.pdata`/`.xdata`, `.sxray` ADDR32NB) mirroring `native_elf.spl`.
3. Then route admission, PE module binding, `check-xray-native-win64-inprocess-e2e.shs`.
