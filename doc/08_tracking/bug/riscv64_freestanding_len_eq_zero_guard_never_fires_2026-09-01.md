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

---

# ROW 2 MEASUREMENT (2026-09-01, fourth session) — a live minimal trigger

Row 2 (`buildrun_sanity_entry.spl`) did NOT reboot-loop for the reason the row-2
summary assumed. Measured under real OpenSBI v1.4 `-bios fw_payload`:

- The OpenSBI banner appears **ONCE**. The `[buildrun]` banner appears 67 times.
  So the machine never resets; the GUEST re-enters `spl_start` repeatedly.
- The cause is now named on serial: `[rv64] FATAL bump heap exhausted (low half)
  - rv_alloc returned NULL`, i.e. `baremetal_stubs.c`'s half of
  `__heap_start..__heap_end` is consumed and the caller stores through NULL.
- It was SILENT before because the exhaustion report lived in `malloc()`, which
  `rt_alloc`/`calloc`/`realloc` and every in-TU `rv_alloc(...)` call site bypass.
  Moved to `rv_alloc()` in `arch/common/baremetal_bump_heap.h` behind
  `RV_HEAP_EXHAUSTED_REPORT()` (default no-op for other includers).

## It is a runaway, not a sizing problem

Growing the heap 64M -> 384M (`__heap_size` in `arch/riscv64/linker.ld`, with
`DEFINED(__heap_size) ? ... : 64M` in the common script so riscv32 is untouched)
only cut the restarts 67 -> 10. 192 MiB is consumed parsing an 8-line program.

With the program reduced to `fn main():\n    print "..."\n`, the WHOLE row runs
green in-guest — frontend, `MirLowering.lower_module`, and
`interpret_hir_module` — printing `BUILDRUN_SIMPLEOS_RISCV64_OK sum=42
nonce=<nonce>` and `[buildrun] build-and-run row exited rc=0`, with **zero**
16 MiB heap ticks. So MIR lowering in-guest is fine.

## The trigger, bisected in-guest over 4 boots

Successive `parse_and_build_module` calls on variants, in one boot each:

| variant | result |
|---|---|
| `fn main():\n    print "x"\n` | ok |
| `fn f(a):\n    print "x"\n` | ok |
| `fn f(a: i64):\n    print "x"\n` | ok |
| `fn f(a: i64, b: i64):\n    print "x"\n` | ok |
| `fn f() -> i64:\n    print "x"\n` | ok |
| `fn f(a: i64) -> i64:\n    print "x"\n` | ok |
| `fn f():\n    1\n` | ok |
| `fn f():\n    1 + 2\n` | ok |
| `fn f() -> i64:\n    1\n` | ok |
| **`fn f(a):\n    a\n`** | **never returns; consumes the whole arena** |
| `fn f(a: i64) -> i64:\n    a\n` | never returns |

Type annotations, return types, parameter count and arithmetic bodies are all
INNOCENT. The single discriminating construct is a **statement that is a bare
identifier expression**. `1` as a body is fine; `a` is not.

This is freestanding-only: the same frontend parses bare identifiers constantly
on the host.

## Why this record

A parse loop that never advances, allocating per iteration, is exactly the shape
this record's fail-open predicts: `while i < toks.len()` and `toks.len() == 0`
disagreeing lets a zero-progress branch repeat forever. That is a HYPOTHESIS,
not yet measured — the guilty loop has not been located.

## Reproduce

`examples/09_embedded/simple_os/arch/riscv64/buildrun_sanity_entry.spl`, call
`parse_and_build_module(_pp_preprocess_conditionals("fn f(a):\n    a\n"), p)`
and boot row 2. Fast cycle: entry-only `native-build` ~60s, fw_payload + boot
~4 min.
