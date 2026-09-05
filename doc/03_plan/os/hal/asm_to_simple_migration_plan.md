# Plan — Asm to Simple Migration (HAL)

**Status:** Plan (2026-08-28). Design:
`doc/05_design/os/hal/asm_embedded_hal_and_dual_run.md`. Evidence:
`doc/01_research/os/hal/hal_asm_embedding_dual_run_survey_2026-08-28.md`.
Policy: `doc/07_guide/os/hal/pure_simple_hal.md`.

Execution model: mechanical lanes on Haiku, review gates on Opus, Fable only
for hard problems (`.claude/memory` "Haiku tasks, Opus review"). Every phase
has an acceptance spec; every migration batch is a step-list a Haiku agent
can execute file-by-file without judgement calls.

## Phase 0 — Unblock the toolchain (prerequisite, not HAL work)

Nothing below can be verified with a pure-Simple binary today: every stage
binary SEGVs at `hir 0/1` on any input (survey §0 Q1). This plan does NOT
own that fix (`doc/08_tracking/bug/stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`),
but it gates Phases 2+ on it. Until then, Phase 1 features are implemented
in the pure-Simple compiler source and **verified through the Rust seed's
`native-build`** (works; ~2 min / 2 GB per file) plus `objdump`.

Exit: `sh scripts/check/check-stage-binaries-runnable.shs` PASS.

## Phase 1 — Compiler features (census ranking)

Each feature: implement in `src/compiler/**` (pure Simple) and, where the
seed lacks it, the minimal seed change so migrations can be verified now.
Each lands with a reproduce-first spec and defect-class neighbours
(`.claude/memory` "Fixes need reproduce + similar tests").

| # | Feature | Owner tier | Acceptance spec (must be RED before, GREEN after) |
|---|---|---|---|
| 1.0 | Raw-block `$` escaping (design A.3.1) + E-ASM-DIRECTIVE | Haiku | `test/01_unit/compiler/backend/asm_raw_block_escape_spec.spl`: a raw block containing `and $~0xF, %rsp` native-builds via seed and emits `48 83 e4 f0`; a block containing `.section` is rejected with E-ASM-DIRECTIVE. |
| 1.1 | F1 CSR/sysreg intrinsics (`csr_read/write/set/clear`, `sysreg_*`, `cp15_*`, `msr_*`, `sbi_call`) | Haiku impl / Opus review | `test/01_unit/lib/baremetal/csr_intrinsics_spec.spl`: per intrinsic, `objdump` of a one-call fn contains exactly the expected mnemonic; interpreter shim returns scripted values; `csr.spl:158` TODO deleted. |
| 1.2 | F2 barrier/cache intrinsics | Haiku / Opus | `barrier_intrinsics_spec.spl`: mnemonic match per arch (`fence rw,rw`, `fence.i`, `dmb ish`, `dsb sy`, `isb`, `dc civac`, `mfence`, `clflush`, `pause`, `wfi`). |
| 1.3 | F3 `@naked` honoured (LLVM `naked` + `unreachable`), `@section`, `@align`, `@global`, E-NAKED-BODY/PARAM-USE/CLOBBER | Opus impl (seed + pure) | `naked_no_prologue_spec.spl` + new gate `scripts/check/check-naked-no-prologue.shs` (`--selftest`, fixture with a synthetic trailing `ret` must FAIL). `linux/x86_64/start.S` twin: 28 bytes, no `ret`, `_start` exported. |
| 1.4 | F3 data items: `@section`/`@align`/`@global` on `static`/`const`, `zeroed()`, `size_of` in const-eval | Opus | `asm_data_items_spec.spl`: multiboot header twin bytes equal `as` output; `readelf -S` shows `.multiboot`; page-table `static` lands in `.bss` at 4096 alignment. |
| 1.5 | Clobber syntax `clobbers(...)`, lints RAW-ASM-001/002 | Haiku | `asm_clobbers_spec.spl`: constraint string `~{rax},~{memory}` appears in emitted IR; unknown name E-ASM-CLOBBER. |
| 1.6 | F4 `@volatile`, `@no_reorder`, `@exact_layout` bitfields | Opus | `mmio_volatile_spec.spl`: two volatile stores keep order and width in `objdump`; bitfield write is RMW of the containing word; `.set_raw` is a plain store; E-LAYOUT on overlap. |
| 1.7 | F5 strict codegen `@strict` / `--strict-codegen` | Opus | `strict_codegen_spec.spl`: a loop that `-O3` vectorises is emitted scalar under `@strict`; no `memcpy` libcall introduced. |
| 1.8 | Dual-run runtime (design Part B): `DualRunner`, `ShadowSet`, comparators, ledger writer, `VirtualDevice` façade, record-compare + replay | Opus (Fable for B.5) | `dual_run_shadow_buffer_spec.spl`: a buffer-out pair where the candidate is deliberately wrong in byte 7 → `Trap`, real target untouched; correct candidate → committed once. `dual_run_record_compare_spec.spl`: two MMIO init sequences that differ in order → mismatch; same → replayed exactly once (façade counts). |
| 1.9 | Gate rewrite: `check-dual-run-shadow.shs` reads registry + ledger, no `PAIRS=13` | Haiku | `--selftest` extended: registry with 0 pairs → ERROR; ledger mismatch → FAIL. |

Order: 1.0 → 1.1 → 1.2 (all LOW, unblock the ~100-site batches) → 1.3 →
1.4 → 1.5 → 1.6 → 1.8 → 1.9 → 1.7.

## Phase 2 — Migration batches (`.S` → `.spl`, inline asm → intrinsics)

Rules for every batch (Haiku-executable, no judgement):
1. Never edit the `.S`/C original in the same commit; the twin lands beside
   it and is wired under dual-run or byte-equivalence first.
2. One file per commit; commit message names source, twin, and the
   verification artefact path.
3. Record binary identity with every measurement
   (`readlink -f bin/simple && stat -c '%s %y' ...`).
4. Read `doc/07_guide/os/baremetal/baremetal_simple_codegen_landmines.md`
   before touching any baremetal file.
5. Diff both directions when a twin already exists (`.claude/memory` "Never
   cp between mirror test trees").

### Batch A — inline-asm sites → intrinsics (needs 1.0–1.2)
Files (site counts from census): `src/os/kernel/arch/riscv64/cpu.spl` (30),
`riscv32/cpu.spl` (18), `arm32/cpu.spl` (22), `arm64/cpu.spl` (20),
`{riscv64,riscv32,arm32}/timer.spl` (5/5/1), `baremetal/x86/io.spl` (6 →
`x86_port_*` externs, the `x86_64/cpu.spl` pattern), `*/semihost.spl`
(14 sites — keep the trap thunk asm, replace the mstatus/daif CSR halves).

Per-file steps:
1. `grep -n "asm" <file>` → list sites.
2. For each site whose text is a single `csrr/csrw/csrs/csrc/mrs/msr/mrc/mcr/rdmsr/wrmsr/fence*/dsb/isb/dmb/dc */wfi/wfe/pause` → replace with the intrinsic from design A.7 F1/F2. Anything else → leave, add `# asm-keep: <reason>` comment.
3. `bin/simple test test/01_unit/os/kernel/arch/<arch>/` (interpreter shim path) must stay GREEN.
4. Seed `native-build` the file's smallest caller; `objdump` and assert the same mnemonic set as before (diff of `objdump -d | grep -oE '^\s+[0-9a-f]+:\s+\S+\s+\S+' | sort -u`).
5. Record in `doc/08_tracking/hal/asm_site_ledger.sdn`: file, sites_before, sites_after, kept, verification path.

Target: 126 → ≤ 15 sites (the trap thunks + context-switch/vector bodies).

### Batch B — instruction-only `.S` → `@naked` `.spl` (needs 1.3, 1.5)
Files: `src/runtime/startup/{linux,freebsd,macos,windows}/*/start.S` (11),
`src/lib/nogc_async_mut_noalloc/baremetal/*/semihost_trap.S` (6),
`src/os/libc/simpleos_syscall{,_aarch64}.S`,
`src/os/libc/simpleos_setjmp{,_aarch64}.S`,
`baremetal/test/qemu_{protocol,semihost}_test.S`.

Per-file steps:
1. Create `<dir>/<name>.spl`; for each `.S` symbol create `@naked @global [@section(...)] fn <symbol>(): asm { <body verbatim> }`; drop `.global/.type/.size/.section` lines (attributes carry them).
2. `as` the original → `ref.o`; seed `native-build` the twin → `twin.bin`.
3. `objdump -d` both; strip addresses and rel32 fields; `diff` must be empty. If the twin has a trailing `ret` the batch is blocked on 1.3 — stop, do not "fix" by appending `ud2`.
4. Add the pair to `scripts/check/check-naked-no-prologue.shs`'s fixture list.
5. Wire the build (`src/compiler/80.driver` startup selection / linker script) to accept the `.spl` twin behind `SIMPLE_STARTUP_TWIN=1`; default stays `.S` until Phase 3 flips it.

### Batch C — data-carrying `.S` (needs 1.4)
Files: `src/compiler/70.backend/baremetal/{x86_64,arm,riscv}/crt0.s`,
`src/runtime/startup/baremetal/*/start.S` (6), `src/os/kernel/arch/arm64/boot/crt0.S`,
`src/os/kernel/arch/arm32/cosmos/cosmos_start.S`, `src/os/libc/simpleos_crt0{,_aarch64}.S`.

Per-file steps: as Batch B plus: every `.section/.align/.skip/.long/.quad/.word/.byte` data run becomes a `@section @align @global static/const` item (design A.5); verification adds `readelf -S` section list equality and `nm --size-sort` symbol sizes equality with `ref.o`; QEMU real-firmware boot lane for the arch must reach the same first milestone (`__spl_start_bare` / first serial line) — board-runnable rule applies.

### Batch D — C twins under dual-run (needs 1.8, 1.9, F2)
Pairs from the census C-twin list, in this order (pure/buffer-out first,
device-effect last): `runtime_any_ops.c`, `runtime_contracts.c`,
`runtime_string_ffi.c`, `runtime_time.c`/`runtime_timestamp.c` (extends the
6 wired timestamp pairs), `runtime_packed_span.c`, `runtime_legacy_core.c`,
`runtime_memory.c`, `runtime_pool.c` (shadow-state), `runtime_memtrack.c`,
`runtime_coverage_core.c`, `runtime_terminal.c`, `runtime_hosted_fs.c`,
then `baremetal/runtime_port_io.c` + `dma_*.c` (record-compare), then
`runtime_simd_{utf8,search,case}.c` under `@strict` (F5).

Per-pair steps: write the Simple twin; register in
`c_migration_inventory.sdn` with `mode:`; add cases to the dual-run spec;
run the gate; ledger must show the pair.

## Phase 3 — Soak, flip, delete

- **Stability bar (final values, adopted from design B.8):** per pair,
  ≥ 1,000 comparison cases over ≥ 30 independent runs on ≥ 2 binary
  identities, **zero mismatches**; device-effect pairs additionally ≥ 10
  clean record-compare runs per supported arch; `@naked` twins: byte-equal
  on every supported arch's `objdump` and one real-firmware QEMU boot per
  arch (board where hardware exists).
- A pair below the bar stays in `UseRef+Log`; a mismatch resets its counter
  to zero and files a bug with the ledger row.
- **Flip:** when a pair meets the bar, the Simple twin becomes the
  implementation and C/asm becomes the oracle (still dual-run in test lanes,
  `Trap` policy). Startup `.S` twins flip via the driver default.
- **Delete:** after one further release cycle at the bar with the roles
  flipped, delete the C/`.S` file; the pair leaves the dual-run registry and
  enters the ordinary spec suite. `check-runtime-api-regression-push.shs`
  `--expect-removals` is used for the symbol removals, recorded in the
  commit message.

## Review gates (Opus)

| Gate | When | Checks |
|---|---|---|
| G1 feature review | after each Phase 1 item | spec RED-before/GREEN-after evidence attached; no new unbacked externs (`check-unbacked-extern-ratchet.shs`); mutation-red on the spec (`.claude/memory` SSpec dual check). |
| G2 batch review | after each Batch A/B/C file | `objdump` diff artefact present and empty; `.S` original untouched; ledger row added; binary identity recorded. |
| G3 pair review | after each Batch D pair | registry `mode:` correct for the op class; mismatch fixture proves the comparator bites; no `UseCand` policy. |
| G4 flip review | Phase 3 per pair | ledger meets the bar on ≥ 2 binary identities; QEMU/board evidence for device-effect and control-transfer pairs. |

## Tracking
- `doc/08_tracking/hal/asm_site_ledger.sdn` (Batch A/B/C progress),
  `doc/08_tracking/hal/dual_run_ledger.sdn` (Phase 3 soak), both
  auto-generated by the gate scripts, not hand-edited.
- Plan status row updated in every in-scope commit (`.claude/memory` "Update
  plan doc on change").

| Phase | Status (2026-08-28) |
|---|---|
| 0 toolchain | RED — stage binaries SEGV on any input |
| 1.0–1.7 | not started (1.3 partially: attrs parsed, pure backend emits `naked`, seed drops it) |
| 1.8 | DONE 2026-08-28 (impl_C): `std.nogc_sync_mut.rt_hal.{dual_runner,virtual_device,dual_run_ledger}`; specs `test/01_unit/lib/nogc_sync_mut/rt_hal_dual_run_{shadow_buffer,record_compare,ledger}_spec.spl` (14+8+6 GREEN, RED-before evidence in the lane report). `validate_rt_hal_tags` now accepts typed args (i64/u*/f64/bool/text/[u8]) and only enforces transport/receipt rules on comparator-tagged fns. Hardware apply (`dual_apply_effects_mmio`) exists but no lane runs it yet. |
| 1.9 | DONE 2026-08-28: gate enumerates `# @dual_pair:` annotations (16 pairs: 13 `value-legacy` + 3 DualRunner), reads the run's ledger rows, 7 selftest fixtures (0 pairs → ERROR, ledger mismatch → FAIL). |
| 2 A/B/C/D | D started: 3 pairs on the DualRunner contract (`dual_run_pairs_spec.spl`: parse_i64 value, base64url_decode shadow-buffer, ns16550_putc record-compare vs a source-derived C trace — QEMU-captured trace still owed); 13 value-legacy pairs remain |
| 3 | not started |
