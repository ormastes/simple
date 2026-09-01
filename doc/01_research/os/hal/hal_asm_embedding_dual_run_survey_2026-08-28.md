# HAL Asm-Embedding and Dual-Run Survey (2026-08-28)

**Status:** Research (survey + measured evidence). Base: release/2026-08-27 tip
`3df474c19fd`. Companion docs: policy
`doc/07_guide/os/hal/pure_simple_hal.md`, census
`doc/01_research/os/hal/pure_simple_hal_asm_minimization_2026-08-28.md`,
design `doc/05_design/os/hal/asm_embedded_hal_and_dual_run.md`, plan
`doc/03_plan/os/hal/asm_to_simple_migration_plan.md`.

This document answers two questions with measurements, then surveys what the
tree already has, what is done, and what is missing, so the design and plan
build on real ground rather than assumptions.

---

## 0. Answers first

### Q1 — Can the remaining `.S` files become asm-embedded Simple? Does it cost binary perf? Is the compiler the blocker?

**Measured (2026-08-28, host load ~25):**

| Probe | Binary | Result |
|---|---|---|
| `native-build hello.spl` | `bootstrap/stage2/simple` (27,125,144 B, 2026-08-28 00:07, `simple-bootstrap 1.0.0-RC`) | **SEGV rc=139** at `[build] hir 0/1 step 2/6`, 1.3 s wall |
| `native-build` asm-only fn (no @naked) | stage2 | SEGV rc=139, same step |
| `native-build` @naked fn (no asm) | stage2 | SEGV rc=139, same step |
| `native-build` @naked + asm start.S twin | stage2 | SEGV rc=139, same step |
| `native-build hello.spl` | Rust seed `bin/release/x86_64-unknown-linux-gnu/simple` (60,744,944 B, 2026-08-26) | OK, **113.2 s wall, 2.0 GB RSS** |
| `native-build` @naked + asm twin, AT&T `$~0xF` verbatim | seed | **llc abort (exit 134): `Bad $ operand number in inline asm string`** — 270 s wall |
| same with `$$~0xF` | seed | OK, **144.7 s wall, 2.1 GB RSS**; binary produced |

Emitted machine code for the `@naked` twin of
`src/runtime/startup/linux/x86_64/start.S` (`objdump -d`, seed build) versus
`as --64` of the original:

```
original _start (as)                       emitted my_start (simple native-build)
48 31 ed        xor  %rbp,%rbp             48 31 ed        xor  %rbp,%rbp
48 8b 3c 24     mov  (%rsp),%rdi           48 8b 3c 24     mov  (%rsp),%rdi
48 8d 74 24 08  lea  0x8(%rsp),%rsi        48 8d 74 24 08  lea  0x8(%rsp),%rsi
48 8d 54 fe 08  lea  0x8(%rsi,%rdi,8),%rdx 48 8d 54 fe 08  lea  0x8(%rsi,%rdi,8),%rdx
48 83 e4 f0     and  $-16,%rsp             48 83 e4 f0     and  $-16,%rsp
e8 <rel32>      call __spl_start           e8 <rel32>      call spl_entry
0f 0b           ud2                        0f 0b           ud2
                                           c3              ret        <-- EXTRA
                                           cc cc cc        int3 pad
```

Findings, stated precisely:

1. **The asm body is byte-identical** (7 instructions, 28 bytes, only the
   `call` rel32 differs and that is a relocation). No prologue was emitted
   (no `push %rbp`/`sub $..,%rsp`). Alignment: function placed at 16-byte
   boundary (`0x2480`), same as `as` default for `.text`. **Binary perf of the
   asm itself is unchanged.**
2. **`@naked` is NOT honored by the Rust seed.** A trailing `ret` (0xc3) is
   appended after `ud2` — the function-return epilogue of the Simple `()`
   return. Harmless here (unreachable after `ud2`), but wrong for any stub
   whose asm ends in a `jmp`/`iret`/`mret`/`eret` that must be the last byte,
   and fatal for fall-through vector slots. The pure-Simple backend does emit
   the LLVM `naked` attribute (`src/compiler/70.backend/backend/llvm_ir_builder.spl:226`,
   `attrs = attrs + " naked"`), but that backend cannot currently run (row 1).
   `/usr/bin/grep -rn naked src/compiler_rust/compiler/src` hits only lint
   tables (`lint/checker_core.rs:569`, `lint/types.rs:700`) — the seed parses
   the attribute and drops it.
3. **Asm strings are passed verbatim as LLVM inline-asm templates.** AT&T
   immediates (`$~0xF`) are read as operand references and crash `llc`
   (exit 134, `Bad $ operand number`). Writing `$$` works. This is a concrete
   compiler bug to file (the design §A.3 settles the escaping contract): either
   the frontend must escape `$` in raw `asm {}` blocks, or the grammar must
   state that raw blocks are LLVM templates. Today the answer is undocumented.
4. **Compile-time cost is dominated by seed startup, not asm.** 113 s for
   hello vs 145 s for the asm twin on the same loaded box (single samples;
   the 270 s run included an llc crash and retry path). Both are the Rust
   seed's ~2 GB stdlib-source-load path (`.claude/rules/commands.md`). The
   asm lowering itself (`parse 257 ms`, `hir 201 ms`, `mir 492 ms` in the
   build log) is milliseconds. **Compiling embedded asm is not slow; the
   pure-Simple stage binaries that should compile it crash on every input.**
5. **Section control is NOT honored by the seed either.** Adding
   `@section(".text.boot")` to the `@naked` fn builds cleanly (rc=0,
   107.5 s wall, 2.0 GB RSS) but `readelf -S` shows only `.text`
   (`[14] .text PROGBITS 0x2380`) and `my_start` stays at `0x2480` inside it
   — no `.text.boot` section exists. `@section` is parsed into
   `FunctionAttr.section_value` (`decl_attrs.spl:748`) and only the
   pure-Simple backend consumes it. Same status as `@naked`: parsed,
   dropped by the seed, unverifiable through stage2.
6. **Convertibility split by file content:**
   - *Instruction-only* `.S` (linux/freebsd/macos/windows `start.S` × 11,
     `semihost_trap.S` × 6, `simpleos_syscall*.S`, `simpleos_setjmp*.S`,
     `context_switch`): convert to `@naked` fns with one raw `asm {}` body —
     byte-identical once `@naked` is honored.
   - *Data-carrying* `.S` (`baremetal/x86_64/crt0.s` multiboot header, GDT,
     page tables with `.align 4096`, `.skip`; `arm64/boot/crt0.S`,
     `cosmos_start.S`, baremetal `start.S` × 6): need `@section`/`@align` on
     **data** items and global-label emission, not only on functions. The
     existing `inline_assembly_design.md` §0 already says "keep ABI-sensitive
     boot entry assembly in `.s/.S` until Simple supports naked functions,
     section placement, global labels, and early stack setup" — that gap
     list is still accurate.

**Verdict:** Conversion is feasible with no binary-perf cost for the
instruction bodies; the blockers are (a) `@naked` unhonored in the seed and
unverifiable in stage2, (b) `$` escaping undefined, (c) `@section` dropped by the seed and `@section`/`@align`
for data + global labels not designed, and above all (d) the self-hosted
compiler SEGVs on every input, so no pure-Simple toolchain can currently
produce or verify the result.

### Q2 — Is dual-running real and usable end-to-end?

**Real, but narrow. Two mechanisms exist; neither meets the full contract.**

| Mechanism | What it does | Shadow buffers? | Gates the real effect? |
|---|---|---|---|
| `scripts/check/check-dual-run-shadow.shs` + `src/lib/common/spec/dual_run.spl` (`dual_check_f64`/`dual_check_text`) | Runs one spec (`test/01_unit/lib/common/spec/dual_run_shadow_spec.spl`) that calls the pure-Simple fn and its `rt_*` C oracle on the same inputs, compares the two **return values**, asserts. 13 pairs, all pure functions (floor/ceil, i64_to_text, byte_char, 6 timestamp ops, hash_text, parse_i64, utf8_validate). | **No** — pure functions, no side-effect targets. | **No** — compare-after-the-fact inside a test; production calls the Simple side only. The script header says so: "dual-runs both implementations only inside test specs, not on live production traffic". |
| `@rt(hal, providers: pure+c+rust, effects: plan_then_commit)` (`decl_attrs.spl` `is_rt_hal`/`rt_hal_compare_c`/`rt_hal_compare_rust`; `35.semantics/rt_hal_tag.spl`; `50.mir/mir_rt_hal_boundary.spl`; `src/app/io/rt_hal_isolated_host.spl`) | Compiles a tagged fn so that C and Rust *isolated process* comparators compute a receipt; parent validates and commits. Requires `--rt-hal-plan` (an `EnvAccessPlan`). | Partially — the isolated worker produces a **child-owned result** the parent validates before commit (`mcdc_rt_hal_hardening.md` §7-8). | Design says plan-then-commit; **but** `validate_rt_hal_tags` rejects anything except **zero-argument, non-async, exactly-`i64`-returning** functions: `"E-RT-HAL-SIGNATURE: boundary comparison currently requires zero arguments; canonical argument transport is unavailable"`. So no buffer, no MMIO target, no argument can be compared today. |

Spec call sites for the isolated host exist (`test/01_unit/lib/rt_hal_external_isolation_source_spec.spl`,
`test/01_unit/app/io/rt_hal_v3_plan_provenance_spec.spl`,
`test/fixtures/rt_hal_external/setup_and_compare.spl`,
`test/05_perf/mcdc_rt_hal/rt_hal_fixture.spl`) — they exercise plan
validation and receipt transport, not a HAL operation with a side-effect
target.

**Missing for the full contract** (both impls run → compare → only then
apply to real hardware/data):

1. Argument transport (any signature, not zero-arg i64).
2. Shadow output buffers: allocate a copy of every out-param / mutated
   buffer, run impl A into the real-sized shadow A, impl B into shadow B.
3. Compare step with typed comparators (bytes, f64 with NaN policy, text) —
   `dual_check_*` is the seed of this, but it only handles scalars.
4. Commit-on-match: copy the agreed shadow into the real target; trap (or
   policy-selected fallback) on mismatch. The `plan_then_commit` effect name
   exists; the copy-on-commit for buffers does not.
5. Side-effect classification: MMIO/CSR writes cannot be doubly applied.
   Needs **record-compare** (both impls emit an ordered effect log against a
   virtual device; compare logs; replay the agreed log once) and **replay**
   (run the trusted impl for real, capture inputs/outputs, replay the
   candidate against the captured trace). Neither exists.
6. Async / interrupt-context operations (explicitly rejected today).
7. A soak ledger (per pair: runs, cases, mismatches) that the plan's
   stability bar can read — today the gate's verdict is a single PASS/FAIL
   line with a hard-coded `PAIRS=13`.

---

## 1. Survey — what exists

### 1.1 Policy and census (done)
- `doc/07_guide/os/hal/pure_simple_hal.md` — the 4-rung policy: typed
  bitfield register views → no-reorder/no-elide tags or strict mode →
  intrinsics → asm only for irreplaceable ops. Committed 2026-08-28.
- `doc/01_research/os/hal/pure_simple_hal_asm_minimization_2026-08-28.md`
  — census: 62 standalone `.S` (src: 36 files / 2,543 lines; examples:
  26 / 2,886), 126 real Simple inline-asm sites (~430 lines, 14 HAL files),
  182 C asm statements (~360 lines, 28 files). Class (a) irreplaceable:
  ~2,500 lines in 36 src `.S`. Class (d) pure-perf asm: zero. Caveat carried
  from the census: it was counted at worktree tip `0fce018eda3`, which is not
  an ancestor of the requested base; recount against `3df474c19fd` before
  acting on file lists. The 36 owned `.S` paths listed by `git ls-files` at
  `3df474c19fd` match the census set (`src/runtime/startup/**` 17,
  `src/lib/nogc_async_mut_noalloc/baremetal/**` 8, `src/os/**` 8,
  `src/compiler/70.backend/baremetal/**` 3).

### 1.2 Inline asm language surface
- `doc/05_design/language/language_features/syntax_features/inline_assembly_design.md`
  (2026-02-05, contract §0 2026-04-21): canonical `asm { ... }` /
  `asm volatile { ... }` raw blocks; `asm(...)` operand form legacy; symbolic
  operands designed (Rust-like `in`/`out`/`inout`) but "operand-bound
  `asm(...)` is parsed but currently skipped by Rust HIR lowering". Modes:
  interpreter skips asm, loader preserves, compiler lowers.
- Live sites use the operand form: e.g.
  `src/lib/nogc_async_mut_noalloc/baremetal/riscv/semihost.spl:113`
  `asm volatile("csrrci {mstatus}, mstatus, 0x8", mstatus = out(reg) mstatus)`.
- Pure-Simple lowering: MIR `InlineAsm` (is_volatile, clobbers) →
  `_MirToLlvm/aggregate_intrinsics.spl:547` LLVM `sideeffect` asm.
- Seed lowering: `src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs`
  preserves raw no-operand asm; measured above: template passed verbatim.

### 1.3 Function attributes
- Parsed into `FunctionAttr` (`src/compiler/00.common/_Attributes/decl_attrs.spl:735-775`):
  `entry`, `naked`, `noreturn`, `section(name)`, `interrupt`, `boot`,
  `alloc`/`no_alloc`, gpu/simd/hls fields, `is_rt_hal`,
  `rt_hal_compare_c/rust`, `rt_hal_error`.
- Backend: `callconv_bridge.spl:55` (`@callconv` > `@naked` > `@interrupt` >
  default), `interrupt.spl` (`InterruptAttr{vector, priority, is_naked,
  is_fast, is_noreturn, is_reentrant}` + vector-table generation),
  `llvm_ir_builder.spl:226` emits ` naked`.
- **Missing:** `@align`, `@no_reorder`/`@volatile` (0 hits in
  `30.types`/`70.backend`), `@section`/`@align` on data, global-label
  emission from Simple, register-clobber syntax on raw blocks, seed honoring
  of any of these.

### 1.4 HAL architecture
- `doc/04_architecture/os/simpleos/kernel/simpleos_multiarch_hal.md`
  (2026-04-25, locked): 8 HAL traits in `src/os/kernel/arch/hal.spl`,
  6-arch `@cfg` dispatch, C→Simple port map. Assumes `.S` stays `.S`.
- `doc/04_architecture/os/simpleos/kernel/arm32_privilege_transition_abi.md`,
  `doc/05_design/app/riscv/riscv_smp_cache_hal.md`,
  `doc/04_architecture/riscv_scalar_runtime_v8_csr.md` /
  `doc/05_design/riscv_scalar_runtime_v8_csr.md` — per-arch CSR and cache
  contracts; all use inline asm or C for the ISA ops the census ranks #1/#2.
- `doc/07_guide/os/baremetal/baremetal_simple_codegen_landmines.md` — known
  codegen hazards for baremetal Simple (read before any migration batch).
- `src/lib/nogc_async_mut_noalloc/baremetal/x86/io.spl` (6 asm sites) vs
  `src/os/kernel/arch/x86_64/cpu.spl` (0 sites, extern-backed
  `x86_port_*`) — the existing proof that extern-first works for class (b).

### 1.5 Dual-run / comparator prior art
- `doc/07_guide/infra/c_migration/dual_run_shadow.md` — 13 wired pairs, 12
  deferred (mostly "file under concurrent edit"; one because `rt_str_hash`
  is not in the interpreter extern table).
- `doc/04_architecture/mcdc_rt_hal_hardening.md`,
  `doc/04_architecture/mcdc_hal_runtime_hardening.md`,
  `doc/07_guide/language/rt_hal_attribute.md` — the `@rt(hal)` capsule:
  providers `pure+c+rust`, assurance levels, `plan_then_commit`, isolated
  process comparators, `EnvAccessPlan` receipts. Signature limit as above.
- `doc/04_architecture/gpu_web_differential_oracle.md` /
  `doc/05_design/gpu_web_differential_oracle.md` — differential oracle for
  GPU/web; same shape (two impls, compare) for a different domain.
- `doc/07_guide/os/crypto_dual_backend.md` — crypto dual backend (select,
  not compare).
- `sh scripts/check/check-dual-run-shadow.shs`: fail-closed, verdict-line
  convention, `--selftest` 3 fixtures; `PAIRS=13` hard-coded.

### 1.6 Toolchain state that gates everything
- All tracked/fresh stage binaries SEGV on any `compile`/`native-build`
  input (`.claude/rules/vcs.md` "tracked stage binaries must actually run",
  advisory-RED; reproduced 2026-08-28 on a stage2 built that morning).
- `check-no-unresolved-runtime-symbols.shs` advisory-RED: 83 codegen-emitted
  runtime names undefined in the C runtime archive.
- Seed `native-build` works but costs ~2 min / 2 GB per file.

---

## 2. What is done / partial / missing (matrix)

| Item | Done | Partial | Missing |
|---|---|---|---|
| Policy (4 rungs) | yes | | |
| Census | yes (needs recount at release tip) | | |
| Raw `asm {}` grammar + seed passthrough | yes | operand form skipped by seed | `$` escaping contract, clobber syntax on raw blocks |
| `@naked` | parsed; pure-Simple backend emits attr | | honored by seed; verified anywhere |
| `@section` (fn) | parsed | backend consumption unverified | data sections |
| `@interrupt` | parsed; `interrupt.spl` ABI model | vector-table emission unproven on hardware | prologue contract per arch |
| `@align` | | | everything |
| `@no_reorder`/`@volatile` | | | everything (0 hits) |
| CSR/sysreg intrinsics | | `csr.spl:158` stub TODO | intrinsic surface + lowering |
| Barrier/cache intrinsics | | | everything |
| Dual-run, pure fns, spec-level | yes (13 pairs) | 12 deferred | |
| Dual-run, receipts via isolated host | plan/receipt path | zero-arg i64 only | arg transport, buffers |
| Shadow buffers + commit-on-match | | `plan_then_commit` named | implementation |
| MMIO record-compare / replay | | | everything |
| Soak ledger + stability bar | | | everything |
| Self-hosted compiler that can build any of this | | | stage binaries SEGV |
