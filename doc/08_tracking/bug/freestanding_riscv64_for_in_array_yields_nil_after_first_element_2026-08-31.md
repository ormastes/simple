# Freestanding riscv64: `for x in <array>` yields a good element only on iteration 1 (2026-08-31)

Status: **ROOT CAUSE NOT YET PROVEN — diagnosis narrowed with in-guest evidence.**
No fix shipped. No workaround shipped. Everything below was measured on this
lane, in-guest, under real OpenSBI `fw_payload` (`-bios` only; no `-kernel`, no
`isa-debug-exit`), with a freshly built Rust seed
(`cargo build --release --bin simple`, exit 0).

Supersedes the framing of the task this came from ("appending a loop variable to
a string builder terminates the string after one pass"). That framing is a
SYMPTOM. String concatenation, the string builder, `chars()`, array length, and
explicit array indexing are all **correct**. See the discriminator matrix.

## Reproduction

`examples/09_embedded/simple_os/arch/riscv64/text_primitive_probe_entry.spl`,
built and booted by `scripts/check/run-riscv64-text-probe-opensbi.shs`
(added by this lane; OpenSBI v1.4 fw_payload, `--timeout 1200`).

Subject `tail` = `"user"}` (7 characters).

## Discriminator matrix (one boot, verbatim serial)

| step | shape | result | verdict |
|---|---|---|---|
| 9a | `for ch in tail.chars(): acc = acc + "x"` | `xxxxxxx` | CORRECT — 7 iterations, literal append |
| 9b | `while k < 5: acc = acc + "y"` | `yyyyy` | CORRECT |
| 9g | `g1 + g2`, both runtime substrings, no loop | `"use` | CORRECT — concat of runtime strings is fine |
| 9f | `while fi < 7: acc = acc + tail.substring(fi, fi+1)` | `"user"}` | CORRECT — loop + runtime-string append is fine |
| 9i | `cs = tail.chars()`; `cs[0] cs[1] cs[2] cs[6]` | `"` `u` `s` `}` | CORRECT — explicit indexing is fine, `cs.len()` = 7 |
| 9j | `while ji < 7: acc = acc + cs[ji]` | `"user"}` | CORRECT — loop-carried store of a concat is fine |
| 9d | `for ch in tail.chars(): acc = acc + ch` | `"` | **WRONG** |
| 9h | same as 9d via an explicit temporary | `"` | **WRONG** — not an SSA/store-shape artifact |
| 9e | 9d with a per-iteration trace | see below | **WRONG** |
| 9k | `for ck in cs: ck.len()` vs 1 | EXPECTED, then WRONG ×6 | **WRONG** |

The 9e trace is the decisive one:

```
[probe] 9e ch = "      <- iteration 1, correct
[probe] 9e acc = "
[probe] 9e ch =        <- iterations 2..7, EMPTY
[probe] 9e acc = "
... (×6)
```

**The loop variable itself is empty from iteration 2 onward.** The accumulator is
innocent: it correctly absorbs nothing. 9k confirms the bad elements are not
merely empty strings but fail a `len() == 1` check.

So: the iteration COUNT is right (7), the array is right, `cs[i]` is right for
every i — only the element bound by `for` is wrong, and only after the first.

## What the MIR says

`SIMPLE_DUMP_MIR=1` on a 3-line fixture (`for ch in "abcd".chars()`):

```
Call    { dest: VReg(5),  target: Pure("rt_for_iterable"), args: [VReg(3)] }
Call    { dest: VReg(6),  target: Pure("rt_array_len"),    args: [VReg(5)] }
...
Load    { dest: VReg(13), addr: VReg(12), ty: TypeId(5) }   # raw i64 index
BoxInt  { dest: VReg(14), value: VReg(13) }                 # tag it
IndexGet{ dest: VReg(15), collection: VReg(5), index: VReg(14) }
Call    { dest: None,     target: Pure("rt_pool_safepoint"), args: [] }
```

`BoxInt` before `IndexGet` is DELIBERATE and documented at
`src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs:1906-1913`
("Box the raw i64 index for rt_index_get (expects RuntimeValue)"), and cranelift's
`compile_index_get`
(`src/compiler_rust/compiler/src/codegen/instr/collections.rs:338`) does call
`rt_index_get` with it. The freestanding `rt_index_get` decodes
(`rt_array_get(value, DECODE_INT(index))`). That chain is self-consistent, and
explicit `cs[i]` uses the same chain and works. **A tagged-vs-raw index mismatch
is therefore NOT established** — the earlier hypothesis (index `i` becoming
`i<<3`, index 0 coinciding) fits the symptom arithmetically but is contradicted
by 9i/9j taking the same path successfully. It is recorded here as disproved,
not as the answer.

The two things unique to the `for` shape and absent from the working `while`
shape are `rt_for_iterable` and `rt_pool_safepoint`. Neither has been excluded.

## The finding that blocked further progress, and matters on its own

**The riscv64 freestanding runtime does not fully compile, and the build says so
in a WARNING and then reports success anyway.** From `probe.build.log`:

```
WARNING: 5 boot source file(s) failed to compile; resulting ELF may have undefined refs
Freestanding unresolved symbol check: 34 unexpected symbol(s)
Freestanding unresolved precheck deferred to linker: 33 candidate symbol(s)
Linked (freestanding): .../probe.elf (48 KB)
Build complete: 1 compiled, 0 cached, 0 failed
```

The five failures are all `*.inc.c` **include-fragments compiled as standalone
translation units**: `baremetal_runtime_network_tail.inc.c`,
`baremetal_runtime_services.inc.c`, `rv64_fs_exec_loader.inc.c`,
`rv64_fs_exec_media.inc.c`, and `full_networking_runtime.c`. Representative
errors — `unknown type name 'uint64_t'`, `use of undeclared identifier
'g_rv_vnet'`, `use of undeclared identifier 'i'` — are exactly what a fragment
produces when torn out of its parent TU.

Mechanism: boot-source autodiscovery in
`src/compiler_rust/compiler/src/pipeline/native_project/linker.rs:1960-2110`
walks the `boot/` directory and compiles every `.c` it finds. `file_stem()` on
`baremetal_runtime_core.inc.c` is `baremetal_runtime_core.inc`; there is no
`.inc.c` exclusion anywhere in the filter chain.

Two consequences, both verified:

1. **`baremetal_runtime_core.inc.c` reaches no binary at all.** Nothing in the
   tree `#include`s it (`grep -rn baremetal_runtime_core.inc.c` returns only a
   comment reference in the probe entry), and it is not compiled as a TU either.
   Two separate C edits to it — a `serial_put_hex` probe in `rt_array_get`, then
   one in `rt_index_get`, the second after `rm -rf .simple/native_cache
   .simple/native-objects-*` — produced **no instruction in the linked ELF**
   (verified by `objdump -d`, not by absence of output). This means **PR #179's
   entire riscv64 runtime port (+712 lines, including the `rt_string_builder_push`
   signature fix) is dead code for this lane**, and so is the riscv64 half of the
   `.len()` ABI fix in
   `freestanding_string_len_u32_vs_codegen_i64_abi_2026-08-31.md`. Both were
   correct changes to a file that is never built.
2. Missing symbols are then satisfied at link time (`_stubs_freestanding.o`
   appears in the object dir), so the link is green and the binary runs on a
   partial runtime. This is precisely the "a clean link is not evidence" hazard.

A third, separate defect found on the way: **an absolute-path include into a
different checkout.** `examples/09_embedded/simple_os/arch/riscv64/boot/full_networking_runtime.c`
is tracked in `origin/main` and its entire content is

```c
#include "/home/ormastes/dev/pub/simple/src/os/kernel/arch/riscv64/boot/freestanding_runtime.c"
```

That target is outside the repository, was last modified 2026-08-22, and is
writable by other lanes. It is the only such include in `examples/` or `src/`
(`grep -rln '#include "/home/'`). Any lane that builds riscv64 freestanding is
compiling another worktree's source. Detection is a one-liner:
`grep -rn '#include "/' examples/ src/`.

## What is still open

- Which of `rt_for_iterable` / `rt_pool_safepoint` / a stubbed symbol actually
  corrupts the bound element. Not determined. Do NOT assume the tagged-index
  theory; 9i/9j disprove it.
- Whether repairing the build (below) fixes the row on its own. Untested.
- The same `for`-over-array shape should be re-probed on x86_64 and aarch64
  before assuming the three arches share this cause. The reported x86_64
  (`role=^@^@^@`) and aarch64 symptoms are consistent with it but unmeasured here.

## Suggested next steps, in order

1. Exclude `*.inc.c` from boot-source autodiscovery in `linker.rs` (fragments are
   by convention compiled only via `#include`), and make "N boot source file(s)
   failed to compile" **fatal** rather than a warning — a runtime that does not
   compile must not link. Both are small and independently justified.
2. Wire `baremetal_runtime_core.inc.c` into a real TU (or fold it into
   `baremetal_stubs.c`), so PR #179 and the `.len()` fix take effect. Re-run this
   probe: several rows may fall out at once.
3. Replace the absolute-path include with a relative one, vendoring the external
   file into the repo.
4. Only then re-probe 9d/9e/9k. If still red, instrument `rt_for_iterable` and
   `rt_pool_safepoint` in a file that is genuinely compiled, and confirm the
   instrumentation appears in `objdump -d` **before** booting.

## Artifacts

- Probe entry (extended with steps 9d–9k): `examples/09_embedded/simple_os/arch/riscv64/text_primitive_probe_entry.spl`
- Harness: `scripts/check/run-riscv64-text-probe-opensbi.shs`
- Serial transcript: `build/os/riscv64_probe/probe.serial.log`
- Build log with the five compile failures: `build/os/riscv64_probe/probe.build.log`
