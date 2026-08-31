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

### Excluded by disassembly (not by argument)

- **`rt_pool_safepoint`** — the linked body is `li a0,0; ret`. A no-op. Excluded.
- **`rt_for_iterable`** — the linked body tag-checks the handle, routes
  `hdr.type == 1` (HEAP_STRING) to `rt_string_chars`, and otherwise returns the
  collection verbatim (`ld a0,-32(s0); sd a0,-24(s0)`). For an array it is an
  identity function. Excluded.

### The remaining lead: the two loop shapes take DIFFERENT codegen paths

MIR for a fixture holding both shapes over the same `array<text>` parameter:

```
# shape_while  (WORKS in-guest)
Load   { dest: VReg(8),  addr: VReg(9), ty: TypeId(5) }
BoxInt { dest: VReg(10), value: VReg(8) }
Call   { dest: VReg(11), target: Pure("rt_index_get"), args: [VReg(6), VReg(10)] }

# shape_for    (FAILS in-guest)
Load    { dest: VReg(10), addr: VReg(9), ty: TypeId(5) }
BoxInt  { dest: VReg(11), value: VReg(10) }
IndexGet{ dest: VReg(12), collection: VReg(2), index: VReg(11) }
```

The working shape emits an explicit **`Call Pure("rt_index_get")`**; the failing
shape emits **`MirInst::IndexGet`**. Both nominally reach `rt_index_get`
(cranelift `compile_index_get`,
`src/compiler_rust/compiler/src/codegen/instr/collections.rs:338`), but they are
different lowering paths, and only one of them is wrong in-guest.

**Prime hypothesis (specific, testable, not yet confirmed).** Cranelift's
`MirInst::BoxInt` lowering
(`src/compiler_rust/compiler/src/codegen/instr/mod.rs:1495-1515`) does NOT tag
when the source vreg's type is `ANY` or `TypeId >= 16`:

```rust
let src_ty = ctx.vreg_types.get(value).copied();
if matches!(src_ty, Some(t) if t == TypeId::ANY || t.0 >= 16) {
    // pass the handle through verbatim, no `<< 3`
}
```

If the for-loop's induction vreg is typed `ANY` (or >= 16) in `vreg_types` while
the while-loop's is `I64`, then the for-loop hands `rt_index_get` a **raw**
index. The freestanding `rt_index_get` (`baremetal_stubs.c:495`) opens with
`if (!IS_INT(index)) return NIL_VALUE;`, i.e. `(index & 7) == 0`:

| raw index | `index & 7` | `IS_INT` | result |
|---|---|---|---|
| 0 | 0 | true | decodes to 0 → **element 0, correct** |
| 1..6 | 1..6 | false | **NIL_VALUE** |

That is exactly the observed signature — correct on iteration 1, nil on every
later iteration — and it explains why explicit `cs[i]` (9i/9j) works: that path
emits a real `Call` whose index vreg is typed `I64`, so `BoxInt` tags it. The
earlier note in this record that the tagged-index theory was "disproved" was
wrong about the mechanism, not the arithmetic: the tag is dropped on the
*producer* side, not misread on the consumer side.

**How to confirm, without a boot:** print `ctx.vreg_types` for the BoxInt source
vreg in both shapes (or add a temporary `eprintln!` in the BoxInt arm and
rebuild the seed), and check whether the for-loop's index takes the pass-through
branch. If it does, the fix is in the compiler: either type the for-loop
induction variable as `I64` at MIR lowering
(`mir/lower/lowering_stmt.rs:1906`), or make the BoxInt pass-through guard not
apply to a value the MIR itself declares `ty: TypeId::I64`. Then re-run the
probe: steps 9d/9e/9h/9k must all go green before any real row is claimed.

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

   **Scope note, so this is not overread:** `rt_string_builder_new/push/finish`
   ARE present as real `T` symbols in the linked probe ELF, even though riscv64
   `baremetal_stubs.c` does not define them (verified by direct grep) and
   `core.inc.c` is not compiled. Their provenance was not identified before this
   record was filed. So the accurate claim is: **`core.inc.c` is not compiled and
   is included by nothing** (proven twice by `objdump -d` showing injected
   instrumentation absent, the second time after clearing
   `.simple/native_cache` and `.simple/native-objects-*`). Whether PR #179's
   builder fix has any effect on the shipped binary is therefore **unknown**, not
   proven-dead. Resolve the provenance before acting on that PR.
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

- Confirm or kill the BoxInt pass-through hypothesis above. That is the single
  next experiment and it needs no boot.
- Identify where the linked `rt_string_builder_*` and `rt_for_iterable` bodies
  actually come from (not riscv64 `baremetal_stubs.c`, not the uncompiled
  `core.inc.c`, not `stubs.rs` — whose synthesized stubs carry no such logic).
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

---

## RESOLVED 2026-08-31 — root cause found, fixed, verified in-guest

### The stated hypothesis is DISPROVED. Do not pursue it.

The "BoxInt pass-through guard" theory above — that
`codegen/instr/mod.rs:1495-1515` skips tagging because the for-loop's induction
vreg is typed `ANY` or `TypeId >= 16` — is **wrong, and the guard never fires
for this shape**. Evidence, in the order it kills the theory:

- MIR lowering emits the induction load as
  `MirInst::Load { dest: current_idx, ty: TypeId::I64 }`
  (`mir/lower/lowering_stmt.rs:1899-1903`) and then a real
  `MirInst::BoxInt { value: current_idx }` (`:1908-1911`). The `for` path is
  **not** missing a BoxInt.
- `build_vreg_types` (`codegen/instr/body.rs:78`, arm
  `MirInst::Load { dest, ty, .. } => types_map.insert(*dest, *ty)`) therefore
  stamps `current_idx` as `I64`. `I64` is neither `ANY` nor `>= 16`, so
  `matches!(src_ty, Some(t) if t == TypeId::ANY || t.0 >= 16)` is false and the
  pass-through branch is not taken. The same is true of the second copy of the
  guard in `codegen/cranelift_emitter.rs:715`.
- Confirmed in the shipped artifact: cranelift emitted the tagging call. The
  producer side was innocent all along.

### The actual root cause: an identity `rt_value_int` in the freestanding runtime

`examples/09_embedded/simple_os/arch/riscv64/boot/baremetal_runtime_core.inc.c:956`
defined

```c
/* This runtime has no separate boxed-integer representation ... */
RuntimeValue rt_value_int(RuntimeValue value)
{
    return value;
}
```

That premise was false. The same link contains `baremetal_stubs.c:495`, whose
`rt_index_get` opens `if (!IS_INT(index)) return NIL_VALUE;` — using the very
`TAG_MASK 0x7` / `TAG_INT 0x0` / `ENCODE_INT` macros that `core.inc.c` itself
defines at lines 22-32 and then declined to use.

Cranelift lowers `MirInst::BoxInt` to `call rt_value_int`, so the identity body
handed `rt_index_get` a **raw** index:

| raw index | `index & 7` | `IS_INT` | result |
|---|---|---|---|
| 0 | 0 | true | element 0 — **correct** |
| 1..6 | 1..6 | false | **NIL_VALUE** |

Exactly the observed "correct on iteration 1, nil on 2..7" signature. The
arithmetic in the disproved hypothesis was right; only its location was wrong —
the tag was never dropped, it was **never applied**, by the runtime, not the
compiler.

**Proven at the instruction level in the linked ELF, not by source reading**
(`llvm-objdump -d --disassemble-symbols=... build/os/riscv64_probe/probe.elf`):

```
00000000802017e0 <rt_value_int>:            # BEFORE — identity, no tag
802017e8: sd   a0, -0x18(s0)
802017ec: ld   a0, -0x18(s0)
802017f6: ret

000000008020098a <rt_index_get>:            # strict consumer, from baremetal_stubs.c
8020099a: lbu  a0, -0x28(s0)
8020099e: andi a0, a0, 0x7
802009a0: beqz a0, 0x802009ac              # else -> NIL_VALUE
```

Why the `while` / explicit-`cs[i]` rows were green throughout: `rt_index_get`
takes a **TAGGED** index and `DECODE_INT`s before delegating, whereas
`rt_array_get` (`baremetal_stubs.c:379`) takes a **RAW** one (`int64_t i =
(int64_t)idx;`). That split is the hosted contract too — `runtime_native.c:4951`
calls `rt_array_get(arr, i)` with a bare loop counter. Only the strict
`rt_index_get` entry point was reachable with an untagged index.

### Fix

`rt_value_int` in `baremetal_runtime_core.inc.c` now returns
`ENCODE_INT(value)`, aligning it with the strict consumer in the same link and
with the hosted ABI. The unbox side needed no change: `rt_value_unbox_int`
routes through `simpleos_raw_or_encoded_int`, which accepts either form.

No `.spl` call site was touched, and no compiler behaviour was changed.

### Two claims in this record that are empirically FALSE and are corrected here

1. **"`baremetal_runtime_core.inc.c` reaches no binary at all"** — false on
   `origin/main` today. `nm -a build/os/riscv64_probe/probe.elf` lists
   `baremetal_runtime_core.inc.c` as a STT_FILE symbol, and the `rt_value_int`
   body linked into the ELF is verbatim that file's. It IS compiled, as a
   standalone TU, by the same autodiscovery the record criticises. This matters
   operationally: **do not implement the record's "suggested next step 1"
   (`*.inc.c` exclusion from boot-source autodiscovery) on its own** — doing so
   would delete `rt_value_int` and dozens of sibling definitions from the link
   and make the lane strictly worse. The exclusion is only safe together with
   wiring the fragment into a real TU.
2. **PR #179 is therefore not dead code for this lane.** The record's own scope
   note already flagged its "reaches no binary" conclusion as unresolved; it is
   now resolved in the negative.

Still genuinely open, unchanged by this fix: 5 `.inc.c`-shaped TUs fail to
compile and the build only WARNs (`linker.rs:1960-2110`); and
`examples/09_embedded/simple_os/arch/riscv64/boot/full_networking_runtime.c`
still `#include`s an absolute path into another checkout.

### In-guest evidence, real OpenSBI `-bios fw_payload` (no `-kernel`, no `isa-debug-exit`)

`sh scripts/check/run-riscv64-text-probe-opensbi.shs`, freshly built Rust seed.
Transcripts: `build/os/riscv64_probe/probe.serial.{PREFIX,POSTFIX}.log`.
Diff of the two runs — every changed line, nothing else moved:

```
9d accumulated =  "            ->  "user"}
9c accumulated =  Q            ->  QuserQ}
9e ch/acc      =  6x empty     ->  u s e r " }   (acc builds to "user"})
9e accumulated =  "            ->  "user"}
9h accumulated =  "            ->  "user"}
9k ch.len      =  6x WRONG     ->  6x EXPECTED
```

Rows that were already green stayed green — `9f`, `9i`, `9j` (the while-loop and
explicit-index rows) are byte-identical across the two runs, so the fix
introduced no regression on the tolerant path.

`9c`'s `Q` where a `"` is expected is a **separate, pre-existing** defect (`Q` in
both runs); this fix corrected only its truncation, not the character. `step 1
len-decoded-as-1 = WRONG` is likewise unchanged and out of scope — that is
`freestanding_string_len_u32_vs_codegen_i64_abi_2026-08-31.md`.

### Regression guard

`scripts/check/check-freestanding-rt-value-int-tags.shs` — fail-closed, 6
fatal selftest fixtures, `PASS/FAIL/ERROR` verdict as the last stdout line, 0
definitions scanned is ERROR not PASS. Verified genuinely red-before:

```
# pre-fix source
FAIL — 5 definition(s) checked, untagged rt_value_int in: examples/09_embedded/simple_os/arch/riscv64/boot/baremetal_runtime_core.inc.c
# post-fix source
PASS — 5 definition(s) checked, 0 untagged
```
