# Design — Asm-Embedded HAL and Dual Running

**Status:** Design (2026-08-28). Policy: `doc/07_guide/os/hal/pure_simple_hal.md`.
Evidence: `doc/01_research/os/hal/hal_asm_embedding_dual_run_survey_2026-08-28.md`.
Plan: `doc/03_plan/os/hal/asm_to_simple_migration_plan.md`.

Two parts. Part A is the language/compiler contract that lets the 36 owned
`.S` files (~2,500 lines) and ~111 of 126 inline-asm sites move into `.spl`
without changing the emitted bytes. Part B is the dual-running architecture
that lets a pure-Simple HAL implementation run beside its C/asm twin, with
the real effect gated on agreement, until the pure-Simple side is trusted.

---

## Part A — Asm-embedding contract

### A.1 Goals and non-goals
- **Goal:** an `.spl` file can express everything a `.S` file expresses today
  — entry stubs, vectors, context switch, syscall/setjmp thunks, boot data
  (multiboot header, GDT, page-table reservations) — and the bytes produced
  are identical to `as` on the original, modulo relocations.
- **Goal:** no prologue/epilogue is ever emitted for a `@naked` function
  (measured today: seed appends `ret`; see survey §0 Q1 finding 2).
- **Non-goal:** register allocation for raw blocks. Raw `asm {}` blocks are
  opaque text; operand-bound `asm(...)` keeps its symbolic-operand design
  from `inline_assembly_design.md` and is not redesigned here.
- **Non-goal:** changing the interpreter's "parse and skip" behaviour.

### A.2 Attribute semantics (normative)

| Attribute | Applies to | Semantics | Emission (LLVM path) |
|---|---|---|---|
| `@naked` | fn | Body MUST be exactly one raw `asm {}` block (E-NAKED-BODY otherwise, incl. any Simple statement, any operand-bound asm, any implicit return). No prologue, no epilogue, no `ret`, no stack-protector, no frame pointer setup, no debug spill. Return type must be `()` or `!` (never). Parameters are allowed only as **documentation of the incoming ABI** and are not materialised (E-NAKED-PARAM-USE if referenced). | `define void @f() naked nounwind noinline { call void asm sideeffect "...", "~{memory}"() ; unreachable }` — `unreachable` (not `ret void`) so no epilogue is synthesised. The function is `noinline` always. |
| `@section(name)` | fn, `static` data, `const` data | Places the symbol in `name`. Name is passed through unmodified. For data, `@section` on a `static` array/struct places its bytes; combine with `@align`. | `section "name"` on the global/function. |
| `@align(n)` | fn, `static`/`const` data | `n` power of two, 1..4096 (E-ALIGN-RANGE). For fns: instruction alignment. For data: symbol alignment. | `align n`. |
| `@global` | fn, data | Symbol is exported with external linkage under its **unmangled** Simple name (E-GLOBAL-MANGLE if the name is not a valid asm symbol). Needed so `.S`-era labels (`_start`, `vector_table`, `gdt64_pointer`) keep their names for linker scripts and other asm. | `dso_local` + external linkage + `@name` verbatim. |
| `@interrupt(vector: N [, priority: P])` | fn | As `interrupt.spl` today: arch prologue saves caller-saved + arch-specific state, returns with `iretq`/`mret`/`sret`/`eret`/`bx lr`. `@interrupt` + `@naked` means: **no** save/restore (user writes it), only the vector-table entry is generated. | Arch calling convention per `callconv_bridge.spl`; `naked` as above when combined. |
| `@noreturn` | fn | Unchanged. On a `@naked` fn it is implied. | `noreturn`. |
| `@volatile` | `static` data, struct field, fn (all accesses) | Every read/write is a side-effect: never elided, never merged, never widened/narrowed, never reordered with another `@volatile` access. Does not imply a hardware barrier. | `load volatile`/`store volatile` with the access width of the declared type. |
| `@no_reorder` | fn | Additionally forbids reordering **any** memory op in the fn across `@volatile` accesses and across `asm volatile` blocks (compiler fence at each). Does not emit a hardware fence — use `fence()`/`dmb()` intrinsics for that. | `fence syncscope("singlethread") seq_cst` around each such access; fn attr `optnone`-free (still optimised, only ordering constrained). |
| `@exact_layout` | struct | Field order, widths and padding are exactly as declared; bitfield syntax `name: uN @ bit_lo..bit_hi` is honoured. Rejects fields whose type has no fixed ABI size. | explicit packed struct with computed padding. |

Precedence when combined: explicit `@callconv` > `@naked` > `@interrupt` >
default (unchanged from `callconv_bridge.spl:57`).

### A.3 Raw block text contract
1. The payload of `asm { ... }` is raw text handed to the target assembler
   dialect (GNU AT&T on x86, GNU on arm/riscv). **No template substitution
   happens in a raw block.** The frontend MUST escape every `$` to `$$` (and
   `{`/`}` to `{{`/`}}`) before handing the text to LLVM's inline-asm
   template engine. This removes the measured `Bad $ operand number` llc
   abort (survey §0 Q1 finding 3) and means a `.S` body can be pasted
   verbatim. Filed as bug: "raw asm block passes `$` unescaped to LLVM".
2. Operand-bound `asm(...)` keeps `{name}` substitution (that is its purpose)
   and requires `$` to be written `$$` by the author (documented, lint
   RAW-ASM-001 warns on a bare `$` followed by a digit in an operand form).
3. Local labels: raw blocks may define labels; they are function-local by
   default (`.L`-prefixed automatically on emission for labels not marked
   `@global`). Cross-block references require `@global`.
4. Directives `.section`, `.global`, `.type`, `.size`, `.align` inside a raw
   block are **rejected** (E-ASM-DIRECTIVE) — those are exactly the things
   the attributes above express, and letting them through would silently
   split a function across sections. `.code32`/`.code64`, `.option
   push/pop`, `.arch`, `.cfi_*` are allowed.

### A.4 Register clobber syntax
```simple
asm volatile clobbers(rax, rcx, memory) {
    rdmsr
}
```
- `clobbers(...)` is a comma list of arch register names plus the pseudo
  names `memory` and `flags`/`cc`. Unknown names: E-ASM-CLOBBER.
- Raw blocks in `@naked` fns MUST NOT carry `clobbers` (nothing to preserve;
  E-NAKED-CLOBBER) — the whole register file is the author's.
- Non-naked raw blocks without `clobbers` default to `clobbers(memory)` and
  `volatile`; a lint (RAW-ASM-002) flags a raw block that names a register
  in its text but not in `clobbers`.
- Lowering: LLVM constraint string `~{rax},~{rcx},~{memory}`.

### A.5 Data items in `.spl` replacing `.S` data
```simple
@section(".multiboot") @align(8) @global
const multiboot_header: [u32; 12] = [0xE85250D6, 0, 48, 0 - (0xE85250D6 + 48), ...]

@section(".bss") @align(4096) @global
static page_table_l4: [u8; 4096] = zeroed()

@section(".rodata") @align(16) @global @exact_layout
static gdt64: Gdt64 = Gdt64(null: 0, code: GdtEntry(...), data: GdtEntry(...))
```
Requirements: `const`/`static` initialisers must be compile-time evaluable;
`zeroed()` maps to a `.bss`-eligible zero initialiser; symbol-difference
expressions (`multiboot_header_end - multiboot_header_start`) are written as
`size_of(multiboot_header)`; checksums are computed by the const evaluator.

### A.6 Guaranteed-no-prologue verification
- Acceptance spec per arch: compile a `@naked` fn whose body is
  `asm { ud2 }` (or `ebreak`/`udf #0`), `objdump -d`, assert the symbol's
  bytes are exactly the trap opcode with **no trailing `ret`** and no leading
  frame setup. Pinned by a new `scripts/check/check-naked-no-prologue.shs`
  (same verdict convention as the other gates; `--selftest` with a fixture
  that deliberately emits `ret` and must FAIL).
- Section/alignment check: `readelf -S` shows the requested section;
  `nm --size-sort` and address `& (align-1) == 0`.

### A.7 The five census features

#### F1 — CSR / system-register intrinsics (LOW, kills ~100 spl sites + ~103 C lines)
```simple
# std.baremetal.csr (riscv)          std.baremetal.sysreg (arm64/arm32)
fn csr_read(name: CsrName) -> u64    fn sysreg_read(name: SysRegName) -> u64
fn csr_write(name, v: u64)           fn sysreg_write(name, v: u64)
fn csr_set(name, mask) / csr_clear(name, mask)   # csrs/csrc
fn cp15_read(cp, op1, crn, crm, op2) -> u32       # arm32 mrc
fn cp15_write(cp, op1, crn, crm, op2, v: u32)     # arm32 mcr
fn msr_read(msr: u32) -> u64 / msr_write(msr, v)  # x86 rdmsr/wrmsr
fn sbi_call(ext, fid, a0..a5) -> SbiRet            # riscv ecall to SBI
```
- `CsrName`/`SysRegName` are enums (typo-proof; E-CSR-UNKNOWN); an
  `csr_read_raw(num: u12)` escape exists for vendor CSRs.
- Lowering: **directly to the existing MIR `InlineAsm` node** with
  `is_volatile=true`, fixed template per arch (`csrr $0, {name}` with `=r`),
  clobbers `memory` only for the barrier-implying ones (`satp`, `sstatus`
  writes get `memory`). No new backend machinery.
- Interpreter: raises E-INTRINSIC-HOST unless a test shim is installed
  (`csr_test_shim(Dict<CsrName,u64>)`), so unit specs can run.
- Acceptance: each intrinsic has a spec that `objdump`s a one-call fn and
  matches the exact mnemonic; `src/os/kernel/arch/riscv64/cpu.spl` migrates
  to 0 asm sites; `arch/x86_64/cpu.spl` is the model (already 0).

#### F2 — Barrier and cache-op intrinsics (LOW, dma_*.c 32 lines + barrier halves of F1 files)
```simple
fn fence(order: Fence)      # Fence.{Full, Rw, R, W, I}  -> fence rw,rw / fence.i / dmb ish / mfence
fn isb() / fn dsb(domain)   # arm
fn dc_clean(addr, len) / dc_invalidate(addr, len) / dc_clean_invalidate(addr, len)  # dc cvac/ivac/civac loops, riscv cbo.*, x86 clflush
fn wfi() / wfe() / sev() / hlt() / pause()
fn cpu_relax()              # arch-neutral pause/yield
```
- Same lowering path as F1. `dc_*` take a range and emit the cache-line loop
  in Simple around a single-line intrinsic (`dc_line_clean(addr)`), so only
  the one-instruction primitive is asm.
- Acceptance: `src/runtime/baremetal/dma_*.c` gain Simple twins under the
  dual-run gate (Part B) using record-compare mode (a cache op has no
  observable data result; its effect log is the comparable).

#### F3 — `@naked` / `@section` / `@interrupt` / `@align` / `@global` end-to-end (MEDIUM)
- Exactly the contract in A.2–A.6. Work items: (1) seed honours `naked`
  (emit LLVM `naked` + `unreachable`), `section`, `align`; (2) pure-Simple
  backend: same plus data-item attributes; (3) `@global` unmangled export;
  (4) E-ASM-DIRECTIVE rejection; (5) `$` escaping; (6) the no-prologue gate.
- Acceptance: the `linux/x86_64/start.S` twin (survey §0) produces the
  28-byte body with **no** trailing `ret` and `_start` visible to the
  linker; a QEMU boot of the `x86_64/crt0.s` twin (multiboot header as
  `@section` data) reaches `__spl_start_bare`.

#### F4 — `@volatile` / `@no_reorder` + `@exact_layout` bitfield MMIO views (MEDIUM)
```simple
@exact_layout
struct UartRegs:
    @volatile data: u32 @ 0x00
    @volatile status: u32 @ 0x04
        tx_ready: bool @ bit 5
        rx_avail: bool @ bit 0
    @volatile ctrl: u32 @ 0x08

@no_reorder
fn uart_putc(u: &mut UartRegs, c: u8):
    while not u.status.tx_ready: cpu_relax()
    u.data = c as u32
```
- Field offsets (`@ off`) are mandatory in `@exact_layout` structs with
  `@volatile` fields; overlap or gap without explicit `pad` is E-LAYOUT.
- A bitfield read is a full-width volatile load then mask; a bitfield write
  is read-modify-write of the containing word (documented; for
  write-1-to-clear registers use `.set_raw(mask)` which is a plain store).
- Replaces `rt_mmio_*` externs (`baremetal/mmio.spl`) and enables typed
  device registers. Optimiser contract is the `@volatile`/`@no_reorder` rows
  of A.2; pinned by a spec that compiles a two-store sequence and asserts
  `objdump` order and width.

#### F5 — Strict-codegen / dual-run mode (MEDIUM-HIGH)
- **Strict codegen** = per-fn or per-module mode (`@strict` or
  `--strict-codegen`) where the optimiser keeps source evaluation order for
  all memory ops, never speculates loads, never vectorises, and never
  introduces libcalls (memcpy/memset) — the behaviour a C-with-intrinsics
  twin like `runtime_simd_utf8.c` needs to be compared instruction-for-
  instruction. Lowered as `optnone`-free but with `-O1` pipeline + explicit
  fences; fast-math off.
- **Dual-run** is Part B. F5's compiler half is the strict mode; its
  runtime half is Part B's harness with the SIMD twin candidates as pairs.

---

## Part B — Dual-running architecture

### B.1 Definition
**Dual running**: for one HAL operation, execute BOTH the candidate
implementation (pure Simple) and the reference implementation (C/asm, or a
previously trusted build) on the same inputs, compare all observable
results **before** any effect reaches real hardware or real data, and commit
the agreed effect exactly once. Disagreement traps (default) or falls back
to the reference per policy, and is always recorded.

Today's mechanisms (survey §0 Q2) are **compare-after-the-fact** on pure
functions; this design is the full contract. Glossary entry:
`doc/glossary.md` "Dual running".

### B.2 Roles
```
caller ──► DualRunner<Op>
             ├── shadow_alloc()      : ShadowSet   (copies of every out target)
             ├── run_ref(inputs, shadow.ref)
             ├── run_cand(inputs, shadow.cand)
             ├── compare(shadow.ref, shadow.cand, comparator) : Verdict
             ├── commit(shadow.ref | shadow.cand → real targets)   on match
             └── on_mismatch(policy): Trap | UseRef | UseCand+Log
```
- `Op` is a `@rt(hal, providers: pure+c, effects: plan_then_commit)` fn.
  The existing attribute keeps its meaning; this design **removes** the
  zero-arg/i64 restriction by defining the transport below.
- The reference is the C/asm twin (bootstrap C keeps a Simple twin — policy
  §2). Once a pair passes the soak bar the roles flip: pure Simple becomes
  the implementation, C becomes the oracle (still dual-run in test lanes),
  then C is deleted.

### B.3 Operation classes and modes
| Class | Example | Observable | Mode |
|---|---|---|---|
| **Pure** | floor_f64, utf8_validate, hash | return value | `value-compare` (today's `dual_check_*`) |
| **Buffer-out** | memcpy/memset twin, utf8 decode into buffer, packed_span ops, pool alloc metadata | out-params, mutated buffers, return | `shadow-buffer` — copy each mutable target twice, run each impl into its own copy, byte-compare, commit one copy |
| **State-mutating** | allocator, memtrack, coverage counters | struct/global state | `shadow-state` — snapshot state, run ref, snapshot; restore, run cand, snapshot; compare snapshots; keep one |
| **Device-effect** | MMIO writes, CSR writes, port I/O, DMA cache ops, timer programming | ordered side effects on hardware — **cannot be doubly applied** | `record-compare` or `replay` (B.5) |
| **Control-transfer** | context switch, vector entry, boot entry | machine state, no return | **not dual-runnable in-process**; verified by A.6 byte-equivalence + QEMU trace-compare (B.6) |

### B.4 Shadow buffers
- `ShadowSet` is allocated from a bounded arena (`@no_alloc` contexts use a
  static reservation sized by `result_bytes`/`request_bytes` from the
  `@rt(hal)` attribute — those fields already exist).
- For each `&mut` / out-param of the op: two copies, initialised from the
  real target (so read-modify-write ops see the same starting bytes).
- Inputs are shared read-only; a candidate that writes an input is a
  mismatch by construction (guard page or post-hash on the input).
- Commit = single `memcpy` of the chosen copy to the real target, under the
  caller's lock discipline; the op's `effects: plan_then_commit` is exactly
  this step. Kernel context: commit must be interrupt-safe — the runner
  disables interrupts for the copy when `@no_alloc` + kernel profile.
- Comparator selection by type: bytes (exact), `f64` (NaN-aware, `bit_exact`
  option — reuse `dual_check_f64`), text (exact), struct (field-wise with
  per-field policy, `@compare(ignore)` for padding/timestamps).
- Arguments: transported by value/reference in-process (same address space,
  no serialisation) — this replaces "canonical argument transport is
  unavailable". The isolated-process path (`rt_hal_isolated_host.spl`) stays
  for out-of-process comparators and keeps its receipt model.

### B.5 Device-effect modes
- **record-compare:** both impls run against a `VirtualDevice` façade that
  records `(order, kind, addr, width, value)` instead of touching hardware
  (`@volatile` accesses in dual-run builds are routed through the façade;
  reads return values from a per-op **read script** captured from the
  reference run or supplied by the spec). Compare the two effect logs
  (exact, or with declared commutative groups). On match, **replay** the
  agreed log once to real hardware. Applicable to init sequences, register
  programming, cache maintenance, port I/O.
- **replay:** the reference runs for real, with a recorder capturing its
  reads and writes; the candidate then runs against the recording (reads
  answered from the trace, writes compared in order). Applicable when the
  hardware response is needed to proceed (probing, handshakes). The
  candidate never touches hardware in this mode.
- Reads with side effects (FIFO pop, W1C status) are declared
  `@volatile(read_effect)` so the façade knows one read consumes.
- Timing-sensitive ops (spin-until-ready) compare logs modulo repeated
  polls of the same address (`poll_collapse`).

### B.6 Control-transfer verification (no in-process dual run)
- Byte-equivalence gate (A.6) for `@naked` twins.
- QEMU trace-compare: run reference and candidate kernels under identical
  QEMU config with `-d exec,int` (or `-icount` deterministic), compare the
  first N traps/vectors and register dumps at breakpoints (`.gdbinit`
  driven). Pinned as a lane script; board-runnable rule applies
  (`.claude/rules/board-runnable.md`) — board evidence bar for any board
  claim.

### B.7 Verdicts, ledger, gate
- Every comparison appends to a ledger `doc/08_tracking/hal/dual_run_ledger.sdn`:
  `pair, mode, run_id, cases, mismatches, first_mismatch_repr, binary_identity`.
- `check-dual-run-shadow.shs` reads the ledger and the pair registry
  (`doc/08_tracking/c_migration/c_migration_inventory.sdn` extended with
  `mode:`) instead of a hard-coded `PAIRS=13`; verdict
  `PASS — <n> pair(s) checked, <m> case(s), 0 divergent` unchanged.
- Mismatch policy: `Trap` default in test lanes; `UseRef+Log` in soak lanes;
  `UseCand` is never allowed until the pair has passed the stability bar.

### B.8 Stability bar (input to the plan's soak criteria)
A pair is **stable** when, on the ledger: ≥ 1,000 comparison cases across
≥ 30 independent runs on ≥ 2 binary identities (seed and self-hosted, or two
consecutive self-hosted deploys) with **zero mismatches**, and for
device-effect pairs additionally ≥ 10 clean QEMU record-compare runs per
supported arch. Numbers are a proposal; the plan owns the final values.
