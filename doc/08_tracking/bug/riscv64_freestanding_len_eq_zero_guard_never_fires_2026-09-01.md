# riscv64 freestanding: `x.len() == 0` is FALSE on a collection whose `.len()` is 0

- Status: OPEN
- Date: 2026-09-01
- Lane: `scripts/check/check-simpleos-riscv64-interpreter-in-guest-opensbi.shs`
- Split out of `riscv64_in_guest_dict_values_yields_empty_erased_receiver_2026-09-01.md`,
  whose primary defect (dict writes dropped by the winning `rt_index_set`) is
  fixed. This one is independent and is NOT fixed.

## Symptom

In one in-guest boot under real OpenSBI v1.4 `-bios fw_payload`, over the same
`Dict<SymbolId, HirFunction>` value, with the dict genuinely empty:

```
[probe] len-begin
[probe] len-end            <- ZERO len-tick lines: `while pi < nfn` ran 0 times
[probe] values-begin
[probe] values-end
[probe] nfn-eq-zero=NO     <- `val nfn = hir.functions.len()`; `nfn == 0` is FALSE
[probe] inline-eq-zero=NO  <- `hir.functions.len() == 0` is FALSE
```

`<` says the value is 0. `==` says it is not 0. Both over the same binding.

This is a FAIL-OPEN: the production guard

```simple
if hir.functions.len() == 0:
    serial_println("[interp] FAIL hir module has no functions — nothing to interpret")
```

exists precisely to catch an empty module and **cannot fire in-guest**. It let a
functionless module through to `interpret_hir_module`, which then reported
"module has no main function" — a correct but far downstream symptom that cost
two sessions of investigation aimed at the wrong phase.

## Additional measurement

Unconditional C markers were placed in `rt_len`, `rt_array_len` and
`rt_dict_len` in `baremetal_runtime_core.inc.c` for a whole boot. **None was
entered even once**, while `rt_dict_values` in the same TU was entered 7 times
from the same probe. So `.len()` on this lane is not routed through any of the
three length entry points the runtime defines. Where it IS routed has not been
established.

Note the `.inc.c`-vs-`baremetal_stubs.c` duplicate-definition trap documented in
the sibling record: `rt_len` is one of the duplicated names, and
`baremetal_stubs.c` is the copy that wins the link. Instrumenting only the
`.inc.c` copy therefore proves nothing about `rt_len`, and re-measurement should
instrument `baremetal_stubs.c`'s copy. It does NOT explain `rt_array_len` /
`rt_dict_len`, which are not duplicated.

## Working hypothesis, explicitly UNPROVEN

`.len()` may return a RAW count (the convention `rt_array_len` and `rt_dict_len`
both document) while the literal `0` it is compared against is TAG-ENCODED, so
`==` compares different encodings while `<` happens to terminate correctly. A
`.len()` returning `NIL_VALUE` fits the observations equally well. Do not record
either as the cause until the actual returned value has been printed.

## Next step

Print the raw 64-bit value that `.len()` returns in-guest, alongside the encoded
literal `0` it is compared to, and instrument `baremetal_stubs.c`'s `rt_len`
rather than the `.inc.c` copy.
