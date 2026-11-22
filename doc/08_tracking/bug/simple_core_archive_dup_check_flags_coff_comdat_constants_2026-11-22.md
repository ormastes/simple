# simple-core archive duplicate-leaf check rejects COFF COMDAT float constants on Windows (2026-11-22)

Status: FIXED in `scripts/check/check-simple-core-runtime-smoke.shs` (this change).

## Symptom

With the new Phase 1 seed (release `6816f70c47e`, which includes the #10876 float `%` fix),
every simple-core archive part compiled. The archive step then refused:

```
simple_core_archive_complete=false
error=duplicate_leaf_symbol:_real@3cb0000000000000: core_any_ops core_string
error=duplicate_leaf_symbol:_real@3ff0000000000000: core_any_ops core_string
```

(Windows MSVC, `TARGET=x86_64-pc-windows-msvc`, LLVM 23.)

## Root cause

Under the MSVC ABI, LLVM emits float literals as COFF literal-pool constants named by their
bit pattern (`__real@<hex>`, `__xmm@<hex>`, ...). They live in `IMAGE_SCN_LNK_COMDAT` sections.
`llvm-readobj --sections core_any_ops/mod_0.o` shows each `.rdata` holding them flagged
`IMAGE_SCN_LNK_COMDAT`, and the linker merges duplicates. Both `core_any_ops` and `core_string`
use `1.0` (`0x3ff0000000000000`), so both define `__real@3ff0000000000000`, as `R` in `nm -g`.

The cross-part check, added for `no_mangle_emits_module_qualified_symbols_2026-11-16.md`,
counted every global `T/D/B/R/S` name. It therefore flagged these constants as leaf collisions.
ELF targets put such literals in local `.rodata.cst*` symbols, so the check was only correct there.

## Fix

The check is now the function `duplicate_leaf_symbols`. It ignores names matching
`^__(real|xmm|ymm|zmm)@[0-9a-f]+$`. Every other global symbol defined by two parts still fails
closed.

## Specs

`--selftest` gained two fixtures (8 total, all PASS):
- Reproducing: `coff-comdat-float-constant-is-not-a-collision`. Two parts each define
  `__real@3ff0000000000000`, and no duplicate is reported.
- Generalizing: `real-leaf-collision-still-fails`. Two parts each define `spl_selftest_dup`,
  and the duplicate is reported.

Host note: on this host the first `cc` on PATH is msys2 mingw64, and it cannot run. The
selftest's first fixture compile therefore aborts the script under `set -e` with no message.
That was verified with a `cc` -> LLVM 23 clang shim. This is a pre-existing host issue,
unrelated to this fix.
