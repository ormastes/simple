# Pure-Simple HAL: Inline-Asm Minimization Census and Feature Plan (2026-08-28)

Census base: worktree tip `0fce018eda3` (requested base `86084338c96` is NOT an
ancestor of this tip — `git merge-base --is-ancestor` rc=1; numbers should be
re-checked against the release tip before acting). Scope: `src/os`, `src/runtime`,
`src/lib/nogc_async_mut_noalloc`, `examples/09_embedded/simple_os/arch/**`,
`src/compiler/70.backend/baremetal` runtime shims. Vendored code excluded per
CLAUDE.md Owned-Code Scope.

## Q1 — How much MUST remain Simple-with-asm?

**Headline: only ~2,500 lines of asm text across 36 src/** files are
architecturally irreplaceable (class a). Everything else — ~111 of 126 Simple
inline-asm sites and ~200 of 360 C inline-asm lines — is eliminable with
features that mostly already half-exist in the compiler.**

Raw census:

| Population | Files | Sites | Lines |
|---|---|---|---|
| Standalone `.S`/`.s` (src/** + examples) | 62 | — | 5,429 (src: 36 f / 2,543 ln; examples: 26 f / 2,886 ln) |
| Simple `asm volatile(` / `asm """` sites | 14 (+4 compiler-internal, excluded) | 126 | ~430 block lines |
| C `__asm__`/`asm volatile` statements | 28 | 182 | ~360 statement lines |

Convention (stated explicitly): "must remain asm" means asm text must remain
*in the source* even after all proposed features land. CSR/MSR access is
architecturally asm at the ISA level, but an intrinsic (`csr_read`) removes the
asm from `.spl` source — so those sites are class (c), not (a). Counting CSR
sites as (a) instead would add ~100 sites / ~270 lines to class (a).

### Per-class

| Class | Files | Lines | Content |
|---|---|---|---|
| (a) irreplaceable | 36 src `.S` + entry stubs | ~2,500 | crt0/start.S boot entry (pre-stack, naked), exception vectors, context switch (`x86_64/boot/context_switch.s`), syscall entry, setjmp (`simpleos_setjmp*.S`), AP trampoline, user-mode first-entry, semihost trap thunks. With `@naked` fully wired these can *move into* `.spl` files as contained asm strings, but the asm text itself stays. |
| (b) replaceable today | 3 spl files (~11 sites, ~15 ln) + 2 C files | ~30 | x86 port I/O (`baremetal/x86/io.spl`, 6 sites) — `runtime_port_io.c` extern shims exist and `src/os/kernel/arch/x86_64/cpu.spl` already proves the pattern (0 asm sites, imports `x86_port_*`); MMIO — `rt_mmio_*` externs in `baremetal/mmio.spl`; `serial_test_kernel.spl`. |
| (c) needs a feature | 11 spl files (~115 sites, ~415 ln) + ~10 C files (~200 ln) | ~615 | CSR/sysreg access: `arch/{riscv64,riscv32,arm32,arm64}/cpu.spl` (30/18/22/20 sites) + `timer.spl` (5/5/1) are almost entirely csrr/csrw, mrs/msr, mrc/mcr; C twins: `freestanding_runtime.c` (53 ln — verified: 11 csr/fence/wfi mnemonics + rdtime + SBI `ecall`; the ecall halves need an `sbi_call` intrinsic alongside CSR), `starfive_runtime.c` (32 ln, 8 csr/fence verified), `cosmos_mmu_cache.c` (18 ln, 11×mcr+7×mrc), `cosmos_smp_gic.c`, DMA cache/barrier ops (`dma_*.c`, 32 ln), semihost traps (14 sites/74 ln in `*/semihost.spl`). |
| (d) pure-perf asm | 0 | 0 | None found. Perf-motivated low-level code is C-with-intrinsics (`runtime_simd_*.c`, 4,019 ln), not asm — it is a Simple-twin/strict-codegen target, not an asm target. |

### Per-arch (standalone .S + spl inline-asm sites)

| Arch | .S files | .S lines | spl asm sites |
|---|---|---|---|
| x86/x86_64 | 20 | 2,129 | 8 (x86_64 itself: 1 — already extern-backed, the model to copy) |
| aarch64/arm64 | 12 | 1,263 | 25 |
| arm32 | 8 | 783 | 31 |
| riscv (32/64/common) | 15 | 711 | 58 |
| generic/other | 7 | 543 | 4 |

## Q2 — Features ranked by asm-sites-eliminated per cost

Existing support found (grep 20.hir/30.types/70.backend): MIR `InlineAsm` node
with `is_volatile`/clobbers lowered to LLVM `sideeffect` inline asm
(`_MirToLlvm/aggregate_intrinsics.spl:547`); HIR `FunctionAttr` already carries
`@entry/@naked/@noreturn/@section/@interrupt` **and** `is_rt_hal` +
`rt_hal_compare_c/rust` (`hir_definitions.spl:52`); dual-run shadow gate live
with 13 C↔Simple pairs (`check-dual-run-shadow.shs`). Cleanly missing:
`no_reorder` — 0 hits anywhere in 30.types/70.backend.

1. **CSR/system-register intrinsics** (`csr_read/csr_write`, `sysreg_read/write`
   covering mrs/msr + mrc/mcr) — eliminates ~100 spl sites (all 4 cpu.spl + 3
   timer.spl) and ~103 C lines. `csr.spl:158` is already a stub TODO waiting for
   exactly this. Cost: LOW — lower to the existing InlineAsm MIR node internally;
   no new codegen machinery.
2. **Barrier + cache-op intrinsics** (fence/fence.i, dsb/isb/dmb, dc cvac/ivac)
   — eliminates the 6 `dma_*.c` files' asm (~32 ln) plus barrier portions of
   (1)'s files; prerequisite for pure-Simple DMA drivers. Cost: LOW (same path).
3. **`@naked` + `@section` + `@interrupt` wired end-to-end** — attrs already
   parse into HIR; finishing backend lowering lets crt0/vectors/trap entries
   (class a) migrate from 39 `.S` files into `.spl` files holding contained asm
   strings — the user's "bootstrap keeps its C/asm but gains a Simple twin"
   shape. Cost: MEDIUM.
4. **Volatile/MMIO bitfield-typed register views with no-elide/no-reorder
   guarantees** — `rt_mmio_*` externs already exist (b), but in-language MMIO
   needs an optimizer-respected `@volatile`/`@no_reorder` tag (currently 0
   support) + `@exact_layout` bitfield structs. Eliminates the extern-C MMIO
   shims and enables typed device registers. Cost: MEDIUM (optimizer fences +
   layout checking).
5. **Strict-codegen / dual-run mode for hot loops** — prior art is live:
   `is_rt_hal`+`rt_hal_compare_c` attr and the 13-pair dual-run gate. Extend to
   the C-twin candidates below; no class-(d) asm exists, so this targets C, not
   asm. Cost: MEDIUM-HIGH (SIMD codegen quality gates the `runtime_simd_*` set).

### C-runtime pure-Simple-twin candidates

48 owned top-level `src/runtime/*.c`, 42,371 lines. ~20 files ≈ 10.5k lines are
plausible pure-Simple twins (exist mainly because Simple lacked
volatile/bit-layout/SIMD features, not because C is required):
`runtime_pool.c` (1,292), `runtime_memory.c` (663), `runtime_legacy_core.c`
(843), `runtime_simd_utf8/search/case.c` (1,806, gated on feature 5),
`runtime_packed_span.c` (201), `runtime_any_ops.c` (47), `runtime_contracts.c`
(45), `runtime_string_ffi.c` (13), `runtime_time.c`/`runtime_timestamp.c`
(186), `runtime_memtrack.c` (328), `runtime_coverage_core.c` (257),
`runtime_terminal.c` (139), `runtime_hosted_fs.c` (36), plus the
`baremetal/runtime_port_io.c` + `dma_*.c` set once features 1-2 land.
Platform-API bridges (SDL/GLFW/OpenSSL/sqlite/win32/cocoa, ~7k ln) stay C.

Raw census lists: session scratchpad `hal/` (asm_files_wc.txt,
spl_asm_real2.txt, c_asm_sites.txt).
