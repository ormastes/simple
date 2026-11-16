# `nand_onfi.spl` divides an array `.get()` result (`T?`) and demotes the NVMe emu module to the interpreter

- **Date:** 2026-11-17
- **Status:** OPEN
- **Severity:** Low (correctness fine; module runs 100-1000x slower under the interpreter)
- **Area:** `examples/09_embedded/simpleos_nvme_fw/emu/nand_onfi.spl:119-120`

## Summary

`me onfi_exec(ch: Ch)` does `val ppn = me.ch_addr.get(c)` then
`val bi = ppn / PAGES_PER_BLOCK`. `Array.get(i)` returns `T?`, and HIR lowering
rejects arithmetic on an unnarrowed optional, so JIT lowering of
`examples/09_embedded/simpleos_nvme_fw/emu/test_emu.spl` fails:

```
[jit-fallback] HIR lowering error: Unsupported feature: cannot apply `Div` to an optional value
that has not been unwrapped; `if x != nil:` does not narrow `T?` to `T` ...
```

and the whole module is demoted to the interpreter. `ALL EMU SELFTESTS PASS` still prints.
Other `.get(...)` results in the same file (`op`, `bad_block.get(bi)`) are used in
comparisons only. Found while verifying the record-unit scalar erase (the earlier
`ppa_to_ppn` `.value` demotion is fixed by that change).

## Fix direction

Unwrap at the use site (`val ppn = me.ch_addr.get(c) ?? 0`, or index `me.ch_addr[c]`),
then re-run `bin/simple.exe run examples/09_embedded/simpleos_nvme_fw/emu/test_emu.spl`
and confirm no `[engine-demotion]` line. Not fixed here.
