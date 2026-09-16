# RISC-V Priv/MMU/RV64 Regression Findings (2026-07-21)

**Investigation scope:** Verify BUG-RISCV-002 and BUG-RISCV-003 against current source  
**Source paths:** `src/lib/hardware/rv32i_rtl/`, `src/lib/hardware/rv64gc_rtl/`  
**Method:** git diff analysis, current source verification, architectural intent

---

## BUG-RISCV-002: RV32 Privileged/MMU/PMP Modules Disconnected

### Verdict: OVER-FRAMED for PL core (intentional bare-metal), REAL for generated lane (placeholder gap)

### Current State Analysis

**RV32I PL Core (`src/lib/hardware/rv32i_rtl/core.spl`):**
- Direct address routing: `val imem_addr = pc` (line 147), `val dmem_addr = alu_res.result` (line 194)
- No privilege state in `CoreState`: only `pc`, `halt`, `semi_*` fields (lines 32-40)
- No Sv32 MMU translation
- No PMP enforcement
- No CSR file in state
- SYSTEM instructions halt immediately (line 265-266)

**Exported but disconnected modules exist:**
- `csr.spl` (10,725 bytes) — Machine-mode CSRs
- `csr_s.spl` (6,230 bytes) — Supervisor-mode CSRs  
- `trap.spl` (7,851 bytes) — Trap handling (MRET/SRET)
- `mmu_sv32.spl` (17,949 bytes) — Sv32 page-table walk

**Root cause:** The production FPGA PL cores (`examples/09_embedded/fpga_riscv/rtl/`) are **intentionally M-mode baremetal** for serial shell operation, not Linux. The audit's "Linux cannot execute" claim is by design, not a bug.

**Generated-RTL lane:** The modules are **placeholder-grade** (memory records `authoritative_rtl_provenance=none`, `formal_gate=placeholder-rejected`). This is a genuine gap for a future Linux-capable generated lane, not the baremetal PL core.

### Recommendation
- **PL core:** NO FIX NEEDED — document as baremetal semihosting-only, not Linux-capable
- **Generated lane:** Keep placeholder classification; if Linux support is planned, file architectural plan with implementation cost estimate

---

## BUG-RISCV-003: RV64 Protected Core Regression (CONFIRMED)

### Verdict: REAL REGRESSION — 371 lines of protected-core implementation removed (790→419 lines)

### Diff Evidence

**Earlier commit with protected core:**
- `80a0d5ee148` "feat(riscv): clock RV64 protected core into SoC" (2026-07-14)
- 790 lines with full Sv39/MMU/PMP integration

**Current state (staged, uncommitted):**
- 419 lines — simplified core missing protection
- File was deleted then re-added as incomplete version

### Removed Features (Confirmed by diff)

| Feature | Removed Evidence | Impact |
|---------|-----------------|---------|
| **PMP state** | `pmp: PmpEntries64` removed from `CoreState64` | No physical memory protection |
| **Memory access routing** | `memory: MemoryAccessState64`, `memory64_cycle()` removed | Direct physical addresses only |
| **CSR read/write** | `csr64_read()`, `csr64_write()` removed | CSRs present but no read/write path |
| **Interrupt handling** | `InterruptCheckResult64`, `trap64_enter()` removed | No external interrupt entry |
| **Instruction legality** | `@hardware core64_instruction_legal()` removed | No fail-closed decoder validation |
| **Privileged instruction checks** | `core64_privileged_instruction_legal()` removed | MRET/SRET/SFENCE.VMA unrestricted |
| **Pipeline phases** | `pipeline_phase`, `fetch_low`, `instruction` removed | No compressed-instruction state machine |
| **SoC integration** | `Core64CycleResult` with `bus_valid/addr/...` removed | No clocked SoC routing evidence |
| **Protected MMU API** | `mmu64_set_satp()`, `ACCESS_*_64` constants removed | MMU state present but unused |
| **PMP CSR routing** | `pmp64_csr_read()`, `pmp64_csr_write()` removed | PMP config unreachable |

### Current Core State (Analyzed from staged file)

**State present but unused:**
```spl
struct CoreState64:
    priv_mode: i64      # Stored, but doesn't affect fetch/load/store
    csr_m: CsrFile64    # Present, no read/write path in core
    csr_s: CsrSMode64   # Present, no read/write path in core
    mmu: MmuState64     # Present, but not invoked on memory ops
    # NO pmp, NO memory, NO pipeline_phase, NO rf
```

**Direct addresses (no translation/protection):**
```spl
val imem_addr = pc              # No Sv39 walk
val dmem_addr = alu_res.result  # No PMP check
```

### Regression Mechanism

Sync commits clobbered the core:
- `115803a7aff` "wip: hourly sync 2026-07-18" 
- `0a749ba7f10` "chore(sync): session work products"
- File was mass-deleted, then incompletely restored from stale WC snapshot

### Recovery Recommendation

1. **Do NOT commit the staged file** — it's a regression artifact
2. **Restore from `80a0d5ee148`** using file-level replay-newest protocol:
   ```bash
   GIT_SSH_COMMAND="ssh -o BatchMode=yes -i ~/.ssh/id_ed25519_this_mac" \
     git fetch git@github.com:ormastes/simple.git 80a0d5ee148
   git show 80a0d5ee148:src/lib/hardware/rv64gc_rtl/core.spl > /tmp/core_protected.spl
   cp /tmp/core_protected.spl src/lib/hardware/rv64gc_rtl/core.spl
   ```
3. **Verify re-landed content** by grep for removed functions:
   ```bash
   grep -q "core64_instruction_legal" src/lib/hardware/rv64gc_rtl/core.spl
   grep -q "PmpEntries64" src/lib/hardware/rv64gc_rtl/core.spl
   grep -q "memory64_cycle" src/lib/hardware/rv64gc_rtl/core.spl
   ```
4. **Add regression test** that fails without protected features
5. **Review downstream integration** (SoC routing, CSR tests, MMU tests)

---

## Cross-Cutting Issues

### Sync-Clobber Pattern
Both bugs surfaced through the same failure mode: parallel-session sync commits capturing stale whole-WC snapshots and reverting landings. Guard improvements needed:
- Pre-push: verify outgoing range doesn't revert product files
- Pre-commit: content-grep origin for key symbols before `jj commit`

### Verification Gap
CI passes with disconnected/missing features because:
- Unit tests check module APIs in isolation (CSR read, MMU walk)
- No end-to-end test validates: SATP write → fetch uses Sv39 → PMP denies → bus request suppressed
- Need VERIFY-001 "non-vacuity calibration" tests

---

## Next Actions

| Priority | Action | Owner |
|----------|--------|-------|
| P0 | Unstage current `core.spl`, restore from `80a0d5ee148` | Hardware team |
| P0 | Add regression guard (grep protected symbols in CI) | Infra |
| P1 | Document PL core as baremetal semihosting-only (not Linux) | Docs |
| P1 | If Linux-capable generated lane is planned, file architecture task | Architecture |
| P2 | Implement VERIFY-001 force-fail tests for privileged/MMU path | Verification |

---

## References

- Audit source: `doc/01_research/hardware/riscv/riscv_rtl_disconnect_audited_bugs_2026-07-21.md`
- Protected-core commit: `80a0d5ee148` "feat(riscv): clock RV64 protected core into SoC"
- RV32 PL core: `src/lib/hardware/rv32i_rtl/core.spl`
- RV64 staged regression: `src/lib/hardware/rv64gc_rtl/core.spl` (staged, uncommitted)
- Sync history: `115803a7aff`, `0a749ba7f10`, `1d6c39a87e8`
