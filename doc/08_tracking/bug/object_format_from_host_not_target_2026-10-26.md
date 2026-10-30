# Object format chosen from the host, not the target triple (2026-10-26)

**Date:** 2026-10-26
**Status:** open
**Evidence:** `C:/dev/hircfg-probe/logs/`, `C:/dev/hircfg-probe/summary.txt`
**Compiler:** `build/s2hw/stage2.exe`, run as `native-build --source src --entry src/hello.spl --target <triple> --cache-dir C:/dev/hircfg-probe/cache --emit-object`
**Severity:** P1 (wrong artifact format)
**Owner:** hircfg lane; fix in progress on branch `work/hircfg-objfmt`

## Rule

The object file format must derive from the target triple, never from the host.

## Symptom

Host is x86_64 Windows. First bytes of the emitted `out/<triple>.o`:

```
aarch64-unknown-linux-gnu.o   64 aa 0b 00   COFF (AArch64, 0xAA64)   -- expected ELF
x86_64-unknown-simpleos.o     64 86 0b 00   COFF (x86_64, 0x8664)    -- expected ELF
riscv64-unknown-linux-gnu.o   7f 45 4c 46   ELF  ok
riscv32-unknown-linux-gnu.o   7f 45 4c 46   ELF  ok
riscv64-unknown-simpleos.o    7f 45 4c 46   ELF  ok
aarch64-unknown-simpleos.o    7f 45 4c 46   ELF  ok
```

The Windows triples (x86_64-pc-windows-msvc, i686-w64-mingw32,
aarch64-w64-mingw32) are legitimately COFF. The two wrong ones are non-Windows
targets whose arch coincides with a Windows-capable arch (x86_64, aarch64),
which is consistent with the format being picked from the host platform plus
arch rather than the OS component of the triple. riscv has no Windows variant,
so it falls through to ELF.

## Impact

aarch64-linux and x86_64-simpleos objects cannot be linked by an ELF linker
(and violate the board-runnable expectation for SimpleOS).

## Suspected area

`src/compiler/70.backend/backend/llvm_native_link_*.spl` object-format selection.
