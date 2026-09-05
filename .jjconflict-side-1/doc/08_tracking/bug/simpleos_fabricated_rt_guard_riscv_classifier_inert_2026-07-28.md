# Fabricated-`rt_*` guard: body classifier is INERT on RISC-V — blocks the rv32/rv64 call sites

- **Status:** FIXED 2026-07-28 — classifier now sees RISC-V, and both call sites are wired. See "Resolution" at the bottom.
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

## Resolution (2026-07-28)

A per-instruction classifier could not be made to work. RISC-V stages a
constant through a temporary (`li a5,1; slli a5,a5,0x1f; mv a0,a5`), and the
production stub objects are compiled with **no `-O`**, so every constant return
also carries a full frame. No single instruction in those bodies says "constant
return"; the fact only exists in the chain. `simpleos_riscv_body_is_trivial_constant`
therefore abstract-interprets the whole body, tracking which registers hold
constants, and `simpleos_trivial_insn_class` keeps handling x86-64/aarch64
unchanged. `simpleos_body_is_trivial_constant` ORs the two, which is safe
because each answers false on anything it cannot fully account for.

Measured, with the shipped predicate driven over real disassembly:

| probe | before | after |
|---|---|---|
| rv64 four unambiguous fakes | **0** | **4** |
| rv32 four unambiguous fakes | **0** | **4** |
| rv64 generated link-stub source (production flags) | 0 | 11 |
| rv32 generated link-stub source (production flags) | 0 | 1 (`rt_pool_safepoint`) |
| x86-64 regression object | 0 | 0 (unchanged) |
| aarch64 regression object | 10 | 10 (unchanged) |

Identical numbers under both `llvm-objdump` and `riscv64-linux-gnu-objdump`,
which print different operand spacing.

False-positive control, in the same probe: `return arg << 31` and
`return arg + 7` compile to `slli a0,a0,0x1f; ret` and `addi a0,a0,0x7; ret` —
byte-for-byte the shape of a constant return, distinguishable only by whether a
constant was established first. Both are correctly reported as real work, at
`-O2` and at `-O0` (where the argument arrives via a stack reload).

One false positive was found and fixed during development: mapping numeric
register names (`x0 -> zero`, `x10 -> a0`) made the analyzer read aarch64's
`add x0, x0, #7` as arithmetic on the zero register and report `return arg + 7`
as fabricated. The mapping is gone; ABI names only, which both disassemblers
print by default. With ABI names only, no aarch64 or x86-64 body can make `a0`
constant, so the RISC-V analyzer is structurally unable to accept a foreign
body — no architecture sniffing required.

### Still open, discovered while fixing this

1. **The x86-64 branch is spelling-dependent, and the deployed tool loses.**
   `simpleos_trivial_insn_class` matches GNU objdump spacing (`xor %eax,%eax`),
   but `find_objdump_portable()` prefers **llvm-objdump**, which prints
   `xorl %eax, %eax`. Measured: a clang-built x86-64 object with ten constant
   returns scores **0** under llvm-objdump. Channel 2 is therefore inert on
   x86-64 in production — the same defect class as this bug, on the arch whose
   baseline was measured. NOT fixed here: the fix is a strengthening that would
   change the x86-64 fabricated set, and the three retained proxy object sets
   the baseline was measured from (`native-objects-tJ7aAf/uSdrJr/wjwkwp`) no
   longer exist, so it cannot be re-baselined without a fresh measurement.
   aarch64 is unaffected — its branch was written for llvm-objdump spacing.

2. **The pure-Simple riscv link route is not reachable end-to-end.** The
   deployed `bin/simple` is the Rust bootstrap seed, whose own Rust linker
   handles freestanding links, so `link_simpleos_riscv64` never runs from the
   CLI today. Consequently the guard call sites are proven correct by
   construction and by probe, but have not been observed firing on a completed
   link. Separately, `link_simpleos_riscv64` links only
   `entry_o + user objects + stub_o + init_o` and supplies no core runtime
   object, so the rv64 smoke closure's ~55 `rt_alloc`/`rt_array_*`/`rt_string_*`
   references resolve from nothing — that route would not link as written.
   Baseline rows were deliberately NOT written for those 55 (see the provenance
   note in `config/simpleos_fabricated_rt_baseline.sdn`): they are an unlinkable
   configuration, not debt.

3. **`allow_weak_real_bodies()`** in
   `test/03_system/check/simpleos_kernel_fabricated_rt_symbol_guard_spec.spl:418`
   still lists 4 symbols where measurement found 6. Different scopes (ELF vs
   objects); left unreconciled, still flagged.
