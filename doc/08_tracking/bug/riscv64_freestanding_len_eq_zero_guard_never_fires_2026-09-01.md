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

---

# MEASURED 2026-09-01 (fifth session): `.len()` on a DICT answers **-1**, not 0

This record's "Working hypothesis, explicitly UNPROVEN" section asked for the
raw value that `.len()` returns in-guest, rather than a comparison result. It
has now been printed, from row 2 under real OpenSBI v1.4 `-bios fw_payload`:

```
[probe] hir-fn-count=-1      <- hir.functions.len(), a Dict<SymbolId, HirFunction>
[probe] mir-fn-count=-1      <- mir.functions.len(), also a Dict
[probe] hir-fn-name=[add] len=3
[probe] names-listed
```

**The answer is `-1`.** Both hypotheses this record offered are therefore wrong:
it is not a raw-vs-tagged encoding mismatch, and it is not `NIL_VALUE` (3). It
is the sentinel `-1`.

That single value explains every symptom recorded here, with no further
assumptions:

- `x.len() == 0` is FALSE — because the length is -1, not 0.
- `while i < x.len()` runs ZERO times — because `0 < -1` is false.
- `rt_len` / `rt_array_len` / `rt_dict_len` are entered ZERO times in a whole
  boot — because the -1 never comes from the runtime at all. The winning
  `rt_len` in `baremetal_stubs.c:628` routes `HEAP_DICT` to
  `simpleos_dict_count` and cannot return -1 on any path; `rt_dict_len`
  (`baremetal_runtime_core.inc.c:2193`) returns `d ? d->len : 0`, likewise never
  -1. The call never reaches either.

Note the scope correction this forces: the previous session measured `.len()` as
INNOCENT on plain `[i64]` arrays (`empty.len() == 0` and the `while i < len`
tick both answered correctly), and that measurement stands. **The defect is
specific to `.len()` on a DICT**, which is why the array probes cleared it and
the `HirModule.functions` probes did not.

This is the signature of the documented native-codegen pitfall in CLAUDE.md —
"`Dict.len()` used to always return `-1`" — which is recorded there as fixed on
2026-08-01 and re-verified 2026-08-09. That verification was on the LLVM/native
path. **This lane is `--backend cranelift --entry-closure` freestanding, and on
it the -1 is still live.** So the CLAUDE.md RESOLVED note should not be read as
covering this backend.

## Why this is now the blocking defect for row 2

Row 2's original hang — the bare-identifier parse loop — is FIXED and verified
(67 guest re-entries -> 1, zero heap exhaustion; see the tagged-bool record).
Row 2 now reaches the run stage and fails with `module has no main function`,
which is exactly the downstream symptom this record predicted.

The probe above also shows `hir.functions` holds exactly ONE entry, `add`, and
the program being built has TWO functions (`add` and `main`). So `main` was
never inserted. A dropped write is ruled out at the store: `simpleos_dict_store`
(`baremetal_runtime_core.inc.c:2139`) is loud on capacity exhaustion
(`[FATAL] rt_dict_set: dictionary capacity exhausted`) and no such line appears
in the serial log; an overwrite is ruled out too, since a colliding key would
have left `main`'s value in the slot, and the name printed is `add`.

The live hypothesis — **stated as a hypothesis, not a finding** — is that a
`while i < something.len()` over a DICT inside HIR lowering runs zero times, or
runs one iteration short, because of the -1. It has NOT been measured, and the
guilty loop has NOT been located. Do not write it up as the cause until the
parsed AST item count and the lowering loop bounds have been printed in-guest.

## Next step

Print the raw `AstModule.items.len()` before lowering (an ARRAY, whose `.len()`
is known-good in-guest) to establish whether the parser produced both functions
or only one. That single number splits the remaining search in half: a 2 blames
HIR lowering, a 1 blames the parser.

---

# FIXED: `.len()` now answers correctly. But it was NOT what dropped `main`.

The `-1` is gone. Measured in-guest under real OpenSBI v1.4 `-bios fw_payload`,
nonce `f75425f438b6c00b`, gate selftest OK (23 fixtures):

| probe | before | after |
|---|---|---|
| `hir.functions.len()` | **-1** | **1** |
| `mir.functions.len()` | **-1** | **1** |

Cause and fix: the Cranelift inline `.len()` fast path
(`inline_runtime_len_value`, `codegen/instr/helpers.rs`) keys on the heap
object's type byte and recognised only 1 (string), 2 (array), 3 (RuntimeDict)
and 6 (SplDict). The riscv64 baremetal runtime tags its dict **11**
(`baremetal_stubs.c:48`, `#define HEAP_DICT 11U`), so an ANY-erased dict fell
through to the `-1` sentinel. `RuntimeDict` is
`{HeapHeader hdr(8), uint64 len, uint64 cap, keys, vals}`, so its length lives
at offset 8 — the same as strings and arrays, NOT SplDict's offset 16.

Guarded by `scripts/check/check-inline-len-covers-baremetal-heap-tags.shs`,
which derives BOTH sides from source (the `#define HEAP_*` set vs. the tags the
codegen function actually compares against) so a new runtime tag cannot be added
without codegen learning it. This class had already been hit for tags 3 and 6,
each fixed by hand with nothing to stop the third.

## A HYPOTHESIS OF THIS RECORD IS NOW REFUTED

The previous section proposed, explicitly as a hypothesis, that a
`while i < something.len()` running zero times on the `-1` was what dropped
`main` during HIR lowering. **That is now disproved.** `.len()` answers 1
correctly and `main` is STILL missing:

```
[probe] hir-fn-count=1
[probe] mir-fn-count=1
[probe] hir-fn-name=[add] len=3
[probe] names-listed
[buildrun] FAIL run error: module has no main function
```

The dict genuinely holds ONE entry. Two functions go in (`add`, `main`); one
comes out. So the loss is upstream of `.len()` entirely, and the `-1` and the
missing `main` were two INDEPENDENT defects that happened to co-occur — the
first merely made the second impossible to see.

Recording the refutation rather than quietly moving on, because the same
plausible-but-wrong inference could easily be made again by the next session.

## What is NOT yet known

Where `main` is lost. It is not established whether the parser produces one
function or two — the natural probe, `parsed.items.len()`, printed **0** while
lowering still produced `add`, which means `AstModule.items` is not the field
carrying the functions on this path, so that probe measured the wrong thing and
is INCONCLUSIVE. It is not evidence that the parser produced nothing.

Both lowering stages report zero errors, so whatever drops `main` does so
silently.

## Next step

Identify the real collection `parse_and_build_module` populates and probe ITS
count in-guest, to split the search: a count of 2 blames HIR lowering, a count
of 1 blames the parser. Do not assume which; the last two assumptions here were
both wrong.
