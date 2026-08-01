# Wave-4: Statement-Like Coroutine / State-Machine Discipline (v1)

Status: design contract, 2026-07-19. Research basis:
`doc/01_research/hardware/nvme_fw_coroutine/embedded_coroutine_statemachine_research.md`
(pattern evaluation + lang-survey verdict: `gen`/`yield` unusable on this
tier — eager interpreter semantics, heap externs, LLVM Yield silently
no-ops; explicit state is the only sound substrate).

Goal (user directive): each core's firmware loop reads as linear,
statement-like code; its progress is a named, persisted, externally visible
state; transitions are legality-checked; the whole thing is easy to debug
and easy to check.

## 1. COROSTATE region (append-only layout change)

- `COROSTATE_BASE = 8448`, `corostate_idx(core) = 8448 + core` (core 0..3 =
  HIL/FTL/FIL/NAND), `IPC_SHM_WORDS` 8448 → **8452**.
- Appended at the END of the map: no landed base moves; existing drift
  oracles stay valid. Invariant updates in `ipc_drift_check.spl`:
  `NAND_DATA_BASE + 4096 == COROSTATE_BASE` and
  `COROSTATE_BASE + 4 == IPC_SHM_WORDS` (replaces the old
  `NAND_DATA_BASE + 4096 == IPC_SHM_WORDS`), plus `corostate_idx(0)==8448`,
  `corostate_idx(3)==8451`, rejects core 4 / -1.
- asm stub `.space` for `_ipc_shm`: 33792 → **33808** bytes. THIS MUST LAND
  ATOMICALLY with the layout change (lane W4c) — a layout bump without the
  asm bump is a silent OOB write into .bss past the region.

## 2. State vocabulary (one shared set, per-core usage subsets)

`logic_coro_core.spl`, fn-per-constant style: `CS_BOOT=0` (pre-gate),
`CS_IDLE=1` (waiting for input), `CS_PUMP_FWD=2` (moving a message toward
NAND), `CS_PUMP_BACK=3` (moving a completion toward HIL), `CS_HALT_DRAIN=4`,
`CS_PARKED=5`, HIL-only: `CS_SUBMIT=6`, `CS_REAP=7`, `CS_VERIFY=8`.
`cs_valid(s)` → 0/1. Numeric on rv32; the HOST harness may map to names for
messages (host-only arrays/strings allowed there).

## 3. Legality + transition (pure)

- `coro_legal(cur, next) -> i32` — explicit if-chain legality table
  (documented pairs; e.g. `CS_BOOT→CS_IDLE|CS_SUBMIT` after gate,
  `CS_PARKED→*` illegal, `CS_HALT_DRAIN→CS_PARKED` only, self-transition
  legal only for CS_IDLE polling).
- `coro_transition_verdict(cur, next) -> i64` — returns `next` if
  `cs_valid` both and legal, else `-1` (fail-closed).
- Drivers NEVER store a corostate word except through the transition helper
  path: compute verdict → verdict `-1` → `ipc_fatal` (rv32) / FAIL + exit(1)
  (host). One writer per corostate word: the owning core only.

## 4. Statement-like authoring convention (the "coroutine" shape)

Each core's loop body is a dispatcher over its resume state; each phase is a
linear block of plain statements that ends in EXACTLY ONE transition call
(the "yield point"). No other control flow may change state. Re-entering the
loop resumes at the stored state — that is the stackless-coroutine resume.
Pattern (illustrative):

```
fn hil_loop_iter(...):            # one resume = one bounded run-to-completion
    val st = shm_get(corostate_idx(0))
    if st == CS_SUBMIT:
        # linear statements: alloc buf, pack msg, push ring
        ...
        return transition(0, st, CS_REAP)      # yield
    if st == CS_REAP:
        ...
```

Locals do NOT survive across yields (protothread rule); anything needed
across a yield lives in shm (buf indices, counters) — already true of the
wave-3 dataplane.

## 5. Debug + easy-check surface

- Cross-core visibility: any core/host debugger reads all 4 corostate words.
- Host harness: last-16 transition ring (host array) + oracle asserting the
  CANONICAL transition sequence for one write→read cycle; end-state oracle
  (all cores CS_PARKED after halt+drain).
- rv32: optional one-UART-char-per-transition trace behind
  `NVME_RV32_CORO_TRACE=1` (default OFF, level-gated per log policy).
- `coro_check.spl`: absolute oracles on legality (each documented legal pair
  passes; representative illegal pairs → -1; invalid state ids → -1),
  rc-calibrated (`exit(1)` convention).

## 6. Lanes + sequencing (hard constraint)

| Lane | Deliverable | When |
|---|---|---|
| W4a | `logic_coro_core.spl` + `coro_check.spl` (NO layout edit) | now |
| W4b | host harness overlay: corostate words simulated in host shm array via the SAME helper fns, transition ring + sequence/end-state oracles added to `ipc_fourcore_check.spl` | after W4a; may pre-stage the +4 words host-side ONLY if kept behind harness-local constants, else waits for W4c |
| W4c | layout append (8452) + drift-check updates + `entry_smp.spl` conversion to corostate dispatch + asm `.space 33808` + trace flag — ATOMIC | after L6 evidence lands |
| W4d | docs/wiki refresh + file LLVM-Yield-silent-no-op bug + research cross-links | after W4c |

W4c is forbidden to land while any in-flight QEMU evidence still uses the
33792-byte stub (OOB hazard §1). All lanes: per-edit safety copies, absolute
oracles, deliberate-red + rc calibration, review before landing.
