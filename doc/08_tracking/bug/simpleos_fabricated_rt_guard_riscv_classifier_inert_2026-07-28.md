# Fabricated-`rt_*` guard: body classifier is INERT on RISC-V — blocks the rv32/rv64 call sites

- **Status:** OPEN — prerequisite for wiring the guard into `link_simpleos_riscv64` / `link_simpleos_riscv32`
- **Severity:** MEDIUM (no false results today; blocks extending the guard to two arches)
- **Area:** `src/compiler/70.backend/backend/llvm_native_link.spl`
  (`simpleos_trivial_insn_class`, ~`:1825`)
- **Filed:** 2026-07-28

## Summary

`simpleos_check_no_fabricated_rt_stubs` landed (commit `309208119eb`) and is
called from `link_simpleos_arm64` and `link_simpleos_x86_64`. The remaining task
was to add the same call to `link_simpleos_riscv64` (~`:2343`) and
`link_simpleos_riscv32` (~`:2508`). **That was deliberately NOT done**, because
the guard would be inert there and would supply false assurance — the exact
fail-open class the guard exists to eliminate.

## Proof

`simpleos_trivial_insn_class` recognises only x86-64 and aarch64 mnemonics
(`endbr64/ret/leave/nop/hlt`, `push/pop`, `mov*`, `xor*`, `movz/movn`). Unknown
mnemonics classify as 0 = "does real work" — a deliberate fail-safe that makes
the guard MISS a fake rather than accuse a real implementation.

RISC-V constant returns are emitted as `li` + `ret`:

    0000000000000000 <rt_fake_zero>:
       0:   li      a0,0
       2:   ret

`li` is unknown, so the body is classified non-trivial. Measured against a probe
object built with `riscv64-unknown-elf-gcc -march=rv64gc -mabi=lp64d -O2`
containing four unambiguous constant-return fakes (`return 0`, `return 1`,
`return 0x80000000ULL`, and the real `rt_riscv_noalloc_pmm_init` body copied
from the generated rv64 stub source) plus one real loop: the classifier reported
**zero** of the four fakes. Channel 2 is therefore fully inert on RISC-V.

## Why channel 1 does not compensate

`link_simpleos_riscv64` links **no `auto_stubs.c`** (verified: `auto_stubs.c` is
compiled only on the x86_64 path). So RISC-V has no weak nil-stub channel, and an
unimplemented `rt_*` fails the link loudly, as on arm64. Channel 1 has nothing to
detect there, and channel 2 — the only channel that applies — cannot see anything.

## Additional, separate fabrication channel on rv64

`link_simpleos_riscv64` resolves symbols with `--defsym=unknown_0=rt_riscv_uart_put`,
`--defsym=unknown_1=_uart_put`, ... `--defsym=unknown_12=_uart_put`, aliasing
unknown symbols onto unrelated real ones. That is its own fabrication mechanism
and the guard does not model it at all. Tracked separately in
`doc/08_tracking/bug/simpleos_riscv64_defsym_unknown_symbol_aliasing_2026-07-28.md`.

## Required before adding the rv32/rv64 call sites

1. Extend `simpleos_trivial_insn_class` with the RISC-V constant-return and
   frame-scaffolding forms (`li`, `mv`, `addi <rd>,zero,<imm>`, `lui`, `c.li`,
   `jr ra`, `ret`), keeping the unknown-mnemonic-means-real-work fail-safe.
2. Re-verify on a real rv64 link that no genuine implementation is accused —
   in particular the memory-map accessors in the generated rv64 stub source
   (`rt_riscv_qemu_ram_base`, `_ram_size`, `_reserved_end`, `_heap_start`,
   `_heap_size`) ARE legitimate constant returns and must be justified in
   `simpleos_rt_symbol_is_optional_backend` or carried in the baseline, not
   silently accepted. Note this makes rv64 a case where the body predicate is
   correct but the symbols are intentional — decide per symbol, with a rationale.
3. Measure an rv64 baseline entry the same way the x86_64 entry was measured,
   then add the call sites.

## Related

- `doc/08_tracking/bug/simpleos_fabricated_rt_guard_weak_real_false_positive_2026-07-28.md` (FIXED by `309208119eb`)
- `doc/08_tracking/bug/simpleos_riscv64_defsym_unknown_symbol_aliasing_2026-07-28.md`
