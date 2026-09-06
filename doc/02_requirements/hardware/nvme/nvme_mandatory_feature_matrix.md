# NVMe Mandatory Feature Matrix (SSpec test obligations)

Status: requirements baseline, 2026-09-01. Authoritative list of MANDATORY NVMe
features that must each carry an SSpec test, keyed to the current modular NVMe
specification family per the hardening plan
(`doc/03_plan/hardware/nvme_ssd_firmware_hardening_design_plan.md` §6.1: Base 2.4,
NVM Command Set 1.3, NVMe over PCIe Transport 1.4, plus Boot/Management Interface
documents — that plan section is the IN-TREE spec ceiling; the version numbers
themselves are the plan's research snapshot, not a document read in this session).

## Sourcing honesty

Provenance per row (unchanged by the 2026-09-01 re-scoring):

- `IN-TREE <file:line>` — grounded in a repo file.
- `MODEL` — from model knowledge of the NVMe specification family, NOT verified
  against a lawfully acquired current document in this session. Every MODEL row
  must be verified against the current NVM Express documents before any
  conformance claim (this restates the plan's own rule at
  `doc/03_plan/hardware/nvme_ssd_firmware_hardening_design_plan.md:368`).

Deliberately, **no clause numbers, register bit positions, or field offsets appear
anywhere in this document** — none are IN-TREE, and a remembered offset presented
as normative would be worse than its absence. Rows name features only.

## Counts up front (RE-SCORED 2026-09-01; supersedes the first scoring below)

- **Mandatory rows (classes 1+2): 20** (16 class-1, 4 class-2 including PRP).
- **Obligation cells: 100** (5 obligations x 20 features).
- **Covered by an in-tree evidence binding: 56** (was 20). **Pending: 44**
  (was 80).
- **Testable at spec TRANSPORT level: 20 of 20 rows** (was 0).
  **Zero blocked features remain** — every one of the 44 pending cells is an
  evidence gap on a drivable path, not an inability to drive the path.
- Ledger: `spec/nvme/coverage.sdn`. Guard:
  `sh scripts/check/check-nvme-spec-coverage.shs` — `PASS — 100 obligation
  cell(s) checked across 20 feature(s), 20 scenario file(s) present, 52
  covered, 44 pending-with-named-blocker` (2026-09-01). Before this re-scoring
  the same guard said **FAIL**, on a rotted blocker plus ten bindings whose
  evidence programs were missing.

### What changed: all four original blockers are CLOSED

Each was re-verified by RUNNING the named program from the repo root and
reading its verdict line — not by grep.

| original blocker | state | evidence (verdict line) |
|---|---|---|
| 1. no controller register file | **CLOSED** | `fw/nvme_reg_defs.spl` + `fw/nvme_reg_file.spl` implement CAP/VS/CC/CSTS/AQA/ASQ/ACQ with enforced RO/RW/RW1C/reserved semantics; `fw/nvme_registers_check.spl` -> `NVME REGISTERS OK` |
| 2. no doorbells / no CQE phase tag | **CLOSED** | `fw/nvme_host_driver.spl` + `fw/nvme_mmio.spl`; `fw/host_equiv_transport_check.spl` -> `HOST EQUIV TRANSPORT OK`. Admin side: `fw/admin_transport.spl`, all 13 admin opcodes SQE-in-memory -> doorbell -> phase-tagged CQE; `fw/admin_transport_check.spl` -> `ADMIN TRANSPORT OK` |
| 3. one-word command payload | **CLOSED** | real 4096-byte `PageData` host -> media -> host; `fw/payload_widening_witness_check.spl` -> `PAYLOAD WIDENING WITNESS OK` |
| 4. rings are struct-field parallel arrays | **CLOSED** for the host path | SQEs are written into queue MEMORY and fetched by the device; witnessed by `fw/prp_wire_witness_check.spl` -> `PRP WIRE WITNESS OK`, which changes the data at the PRP address before the doorbell and requires the device to store the NEW bytes |

Two matrix claims are therefore now FALSE and are struck rather than softened:
"no code touches a doorbell", and "PRP is two base addresses packed into one
word". PRP1/PRP2 are real addresses the device DMAs from.

### The fifth blocker, closed during this session

`arbitration` was the one row that survived the first pass of this re-scoring:
queue pairs could be created over the admin doorbell path, but nothing drove two
queues in competition and measured fairness. A competing-queue harness,
`fw/arbitration_check.spl`, landed mid-session from another lane and was
verified here by running it: verdict `ARBITRATION OK`, with all four bound
tokens confirmed present in the captured log —
`P2 NO STARVATION: the arbiter never served one queue twice running while
another had backlog`, plus named NEGATIVE, RESET and FAULT assertions.
Arbitration's positive/negative/reset/fault cells are therefore covered and
**no NVMe mandatory row is blocked any more.** Its persistence cell stays
pending with the rest.

### The 44 pending cells, by category (evidence gaps, not blockers)

Counted per obligation across all 20 rows, straight out of the emitted ledger:

| obligation | covered | pending | which rows are pending |
|---|---|---|---|
| positive | 20 | **0** | — every row has positive evidence |
| negative | 12 | **8** | abort, async_event_request, features_set_get, get_log_error, get_log_fw_slot, get_log_smart, nvm_flush, nvm_read |
| reset | 9 | **11** | abort, async_event_request, features_set_get, get_log_error, get_log_fw_slot, get_log_smart, identify, io_queue_create_delete, nvm_flush, prp_transfer, status_code_reporting |
| fault | 12 | **8** | abort, async_event_request, features_set_get, get_log_fw_slot, identify, io_queue_create_delete, nvm_flush, prp_transfer |
| persistence | 3 | **17** | every row except nvm_read, nvm_write, nvm_flush |
| **total** | **56** | **44** | |

The dominant gap is **persistence**, and it is now the single largest lever
left: closing it alone would move 17 cells. Only Read/Write/Flush have
power-cycle durability evidence (`fw/durability_check.spl` -> `DURABILITY OK`);
nothing power-cycles and re-reads the register file, the feature store, or the
queue set. Reset-SURVIVAL evidence does exist (`PRESERVED: AQA is not affected
by a Controller Reset`) and was deliberately NOT bound to `persistence`: that
would be a category error, the same one the ledger already rejects for
backpressure-as-negative.

The reset/fault/negative gaps concentrate on the admin-command rows: the opcode
demonstrably travels the doorbell transport, but nothing asserts what survives a
reset, what happens under injected failure, or that a malformed variant of that
specific command is rejected with no state change.

### Per-row delta (covered obligation cells, of 5)

| feature | before | after | note |
|---|---|---|---|
| Controller registers | 0 | 4 | blocker 1 closed |
| Enable/disable handshake | 0 | 4 | blocker 1 closed |
| Controller reset | 0 | 4 | now register-initiated, not a power-cycle analogue |
| Admin SQ/CQ pair | 1 | 4 | dispatch -> transport |
| SQ/CQ doorbell registers | 2 | 4 | |
| CQE phase tag | 3 | 4 | |
| Identify | 1 | 2 | aggregate -> **direct** (`Identify produced a CONTROLLER structure`) |
| Get Log Page - Error | 0 | 2 | |
| Get Log Page - SMART | 1 | 2 | aggregate -> direct |
| Get Log Page - FW Slot | 0 | 1 | |
| Set/Get Features | 1 | 1 | aggregate -> direct |
| Create/Delete I/O SQ+CQ | 2 | 2 | aggregate -> direct on positive |
| Abort | 0 | 1 | transport only, not command semantics |
| Async Event Request | 0 | 1 | transport only, not command semantics |
| Command arbitration | 0 | 4 | blocker closed mid-session by `fw/arbitration_check.spl` (another lane); verified here |
| Status-code reporting | 1 | 3 | |
| Read | 3 | 4 | positive now PRP-backed; fault now direct |
| Write | 3 | 5 | **all five obligations covered** |
| Flush | 2 | 2 | |
| PRP data transfer | 0 | 2 | blocker 3 closed |
| **total** | **20** | **56** | **+36 cells** |

### Controller-initialisation sequence (new, highest-value scenario)

`test/03_system/app/nvme_firmware/generated/nvme_gen_controller_initialization_sequence_spec.spl`
walks the real bring-up in order: read CAP -> program AQA/ASQ/ACQ -> set CC.EN ->
wait for CSTS.RDY -> Identify over the admin queue -> create an I/O queue pair ->
PRP-backed write and read. **Scope stated in the file itself:** the stages are
exercised by THREE in-tree programs, not one, so it proves every stage is
exercised, not that one uninterrupted host session walks all of them.
Measured 2026-09-01: `3 examples, 0 failures`.

### Known cost defect introduced by this re-scoring

Three files — `nvme_gen_nvm_write_spec.spl` (5 covered cells),
`nvme_gen_nvm_read_spec.spl` (4) and `nvme_gen_status_code_reporting_spec.spl`
(3) — now spawn one heavyweight firmware run PER CELL and exceed the test
runner's 900s per-file budget: a TIMEOUT, not an assertion failure. The 3-cell
case shows the driver is total bound-program cost, not cell count. Every token they
assert was independently confirmed by running its evidence program directly.
Filed, with the preferred fix (run each evidence program once per suite instead
of once per cell; `durability_check.spl` alone is bound three times and re-run
three times) at
`doc/08_tracking/bug/nvme_gen_spec_exceeds_runner_budget_after_rescoring_2026-09-01.md`.
**Do not resolve it by unbinding evidence** — a pending cell asserts the ledger
blocker and would go green, converting a real timeout into a false claim of an
admitted gap.

### Honest gating preserved (re-measured against the final ledger)

A pending cell still emits an explicit `BLOCKED:` marker that asserts the ledger
records that exact cell with that exact blocker text. It is NOT a vacuous
assertion, and this was proven by mutation on the final 56/44 ledger: rewording
the pending-reason string turned `nvme_gen_get_log_fw_slot_spec.spl` to
`5 examples, 4 failures` — **exactly its 4 pending cells went red while its 1
covered cell stayed green** — and the ledger was restored immediately after.

`scripts/check/check-nvme-spec-coverage.shs` independently fails a pending cell
with no blocker text, a covered cell whose bound token its program never prints,
and a blocker that has rotted against the firmware tree.

### Historical: the first scoring (2026-09-01, superseded above)

- Mandatory rows 20; testable 12 at function-call dispatch level; 0 at spec
  transport level; 8 blocked on four blockers (register file, doorbells/phase
  tag, one-word payload, struct-field rings). Retained for history; every
  numeric claim in this block is now stale.

## Firmware ground truth (re-measured 2026-09-01)

- I/O opcodes implemented: 5 — Flush, Write, Read, Write Zeroes, DSM/Trim
  (`fw/nvme_types.spl`).
- Admin opcodes implemented: 13 — Delete/Create SQ, Get Log Page, Delete/Create
  CQ, Identify, Abort, Set/Get Features, Async Event Request, FW Commit,
  FW Download, Format NVM (`fw/nvme_admin_types.spl`). **All 13 now travel the
  admin doorbell transport** (`fw/admin_transport_check.spl`:
  `all 13 admin opcodes travelled exec_admin`).
- Controller register file: `fw/nvme_reg_defs.spl` + `fw/nvme_reg_file.spl`,
  driven by `HostNvme.bringup()` / `controller_disable()` in
  `fw/nvme_host_driver.spl`.
- Real page payloads: `fw/nvme_payload.spl` `PageData`; PRP1/PRP2/PRP-list over
  a host DMA region in `fw/nvme_host_driver.spl` (`submit_prp`, `exec_io_prp`).
- Reset/fault/persistence hooks for SSpec authors: register-initiated Controller
  Reset (CC.EN 1->0), CSTS.CFS on an invalid AQA, `power_cycles`,
  `unsafe_shutdowns`, `dirty_since_checkpoint` (`fw/nvme_controller.spl`);
  recovery path `fw/nvme_emu_recovery_check.spl`; decaying-media fault path via
  `nvme_controller_new_emu()`.

## Matrix

Classes: **1** = mandatory for any NVMe controller; **2** = mandatory for the NVM
Command Set; **3** = mandatory-if-advertised; **4** = optional. Class membership
of every row is `MODEL` unless noted. Firmware-status citations are `IN-TREE`.
"testable today?" now reports the level PLUS the covered obligation cells of 5,
so a row that is transport-drivable but thinly asserted cannot read as done.

### Class 1 — mandatory for any controller (16 rows)

| feature | class | provenance | current firmware status | testable today? | remaining gap |
|---|---|---|---|---|---|
| Controller registers CAP/VS/CC/CSTS/AQA/ASQ/ACQ | 1 | MODEL — verify against current Base spec | IN-TREE `fw/nvme_reg_defs.spl`, `fw/nvme_reg_file.spl`; RO/RW/RW1C/reserved enforced | **transport level, 4/5** | persistence: nothing power-cycles and re-reads the register file |
| Controller enable/disable handshake (CC.EN/CSTS.RDY) | 1 | MODEL — verify | IN-TREE: CC.EN 0->1 drives CSTS.RDY 0->1, RDY is not instant, mid-transition CC write ignored | **transport level, 4/5** | persistence |
| Controller reset behavior | 1 | MODEL — verify | IN-TREE, register-initiated: CC.EN 1->0 DISCARDS doorbells/phase/shadow state and PRESERVES AQA/ASQ/ACQ | **transport level, 4/5** | persistence |
| Admin SQ/CQ pair | 1 | MODEL — verify | IN-TREE memory-resident ASQ/ACQ + admin doorbell (`fw/admin_transport.spl`) | **transport level, 4/5** | persistence |
| SQ/CQ doorbell registers | 1 | MODEL — verify | IN-TREE `fw/nvme_mmio.spl`, `fw/nvme_host_driver.spl`; SQ0TDBL/CQ0HDBL, stride from CAP.DSTRD | **transport level, 4/5** | persistence |
| CQE phase tag | 1 | MODEL — verify | IN-TREE: phase bit 16, stale/wrong-phase CQE refused, host phase toggles on the lap | **transport level, 4/5** | persistence |
| Identify (Controller, Namespace, Active NS list CNS values) | 1 | MODEL — verify | IN-TREE over the admin doorbell path; CNS decode in `fw/nvme_admin.spl` | **transport level, 2/5** | reset, fault, persistence; byte-accurate structure layout unverified |
| Get Log Page — Error Information log | 1 | MODEL — verify | IN-TREE; error_count/last_error tracked | **transport level, 2/5** | negative, reset, persistence |
| Get Log Page — SMART/Health log | 1 | MODEL — verify | IN-TREE; SmartLog + media_errors/temperature | **transport level, 2/5** | negative, reset, persistence |
| Get Log Page — Firmware Slot log | 1 | MODEL — verify | IN-TREE; fw_slot tracked | **transport level, 1/5** | everything but positive; also 0 mapped clauses in the extraction |
| Set Features / Get Features (mandatory FIDs) | 1 | MODEL — verify | IN-TREE; Get reads back what Set stored, over the admin doorbell | **transport level, 1/5** | mandatory-FID completeness unverified |
| Create/Delete I/O SQ and CQ | 1 | MODEL — verify | IN-TREE: Create CQ + Create SQ for qid 1 over the doorbell, two admin round-trips | **transport level, 2/5** | reset, fault, persistence |
| Abort | 1 | MODEL — verify | IN-TREE opcode travels the transport | **transport level, 1/5** | nothing asserts what an Abort actually cancelled |
| Asynchronous Event Request | 1 | MODEL — verify | IN-TREE opcode travels the transport; held-CID model | **transport level, 1/5** | nothing asserts which event was reported |
| Command arbitration (round-robin minimum) | 1 | MODEL — verify | IN-TREE competing-queue harness `fw/arbitration_check.spl` -> `ARBITRATION OK`: no starvation, empty queue never selected, no pre-reset advantage, deleted qid never re-selected | **transport level, 4/5** | persistence |
| Mandatory status-code reporting (Invalid Opcode / Invalid Field, fail-closed) | 1 | MODEL — verify | IN-TREE: unsupported admin opcode -> SC_INVALID_OPCODE; over-MDTS write -> SC_INVALID_FIELD | **transport level, 3/5** | reset, persistence |

### Class 2 — mandatory for the NVM Command Set (4 rows)

| feature | class | provenance | current firmware status | testable today? | remaining gap |
|---|---|---|---|---|---|
| Read | 2 | MODEL — verify | IN-TREE, PRP-backed real pages | **transport level, 4/5** | negative |
| Write | 2 | MODEL — verify | IN-TREE, PRP-backed real pages | **transport level, 5/5 — the only complete row** | — |
| Flush | 2 | MODEL — verify | IN-TREE | **transport level, 2/5** | negative, reset, fault |
| PRP data transfer (mandatory for the PCIe transport) | 2 | MODEL — verify | IN-TREE: PRP1/PRP2 are real addresses the device DMAs from; PRP LIST page for >2 blocks; MDTS refusal is pre-transfer | **transport level, 2/5** | reset, fault, persistence |

### Class 3 — mandatory-if-advertised (test before any capability bit is set)

Unchanged by this re-scoring, and still the highest-risk class: each becomes
mandatory the moment the corresponding Identify capability bit (OACS/ONCS —
names only, MODEL) is set.

| feature | provenance | current firmware status | note |
|---|---|---|---|
| Write Zeroes | MODEL — verify | IMPLEMENTED (`fw/nvme_types.spl`) | **Hazard row**: implemented but no Identify bit plumbing exists to advertise it honestly. No advertisement until 5 obligations pass. |
| Dataset Management (Deallocate/Trim) | MODEL — verify | IMPLEMENTED | same hazard as Write Zeroes |
| Firmware Download + Commit | MODEL — verify | IMPLEMENTED; opcodes travel the admin transport | OACS-conditional |
| Format NVM | MODEL — verify | IMPLEMENTED; opcode travels the admin transport | OACS-conditional |
| Volatile Write Cache feature | MODEL — verify | DRAM write buffer exists | if advertised, Flush semantics tests tighten |

### Class 4 — optional (boundary only, not padded)

MODEL, per plan §6.1 P3 row: SGL, ZNS, KV, Subsystem Local Memory, Computational
Programs, multiple namespaces / namespace management, SR-IOV/virtualization,
fabrics transports, Management Interface endpoints. Out of scope for this matrix
beyond noting they must not be advertised.

## Staged ordering (reuses plan §6.1 P0-P3 — do not invent a parallel scheme)

| stage | prerequisite delivered | rows unblocked |
|---|---|---|
| **P0 transport bring-up** — **DELIVERED 2026-09-01** | Controller register file, enable/disable/reset handshake, doorbell + CQE-phase transport over memory-resident rings, `nvme_transport_profiles.sdn` wired to real code, admin doorbell transport for all 13 admin opcodes | DONE: registers, handshake, reset, doorbells, phase tag, transport-level Admin SQ/CQ and Create/Delete I/O queues all re-scored to transport level |
| **P1 block I/O** — **PARTLY DELIVERED 2026-09-01** | Payload widening landed: real 4096-byte pages + memory-resident PRP entries/lists over a host DMA region | DONE: Read/Write/Flush and the PRP row are transport level (Write is 5/5). NOT done: Write Zeroes / DSM promotion out of the no-op-hazard state — no Identify capability-bit plumbing exists |
| **P2 robust operation** — **arbitration DONE; persistence is now the lever** | A power-cycle harness that re-reads registers/features/queues (would close 17 cells — the largest remaining block), interrupt (MSI/MSI-X) model, power-cycle harness that re-reads registers/features/queues power-state/health, firmware slot/update design, telemetry | the 44 evidence-gap cells, FW Download/Commit and Format under the five obligations, VWC advertisement |
| **P3 extensions** | Per plan | class-4 items only, each as a separately profiled module |

## The five test obligations per capability (SSpec-actionable)

Every advertised capability bit and every mandatory row needs all five, per
`...hardening_design_plan.md:368`. Concretely, for capability X:

1. **Positive** — issue the well-formed command(s) X enables through the host
   path: build the SQE in queue memory, ring the doorbell, poll the phase-tagged
   CQE; assert a spec-shaped completion (correct SC, CID, phase tag) and the
   correct data/state effect. P0 has landed, so this is now the REAL path for 19
   of 20 rows — `fw/nvme_host_driver.spl` for the NVM command set,
   `fw/admin_transport.spl` for admin. Never `process_one_io`.
2. **Negative** — issue malformed variants (bad queue id, bad NSID, out-of-range
   LBA, invalid field) and the same opcode with X *not* advertised; assert the
   correct error SC and **no state change** — never no-op acceptance. Fail-closed
   precedent: `fw/nvme_admin.spl:477-599` checks.
3. **Reset** — perform X, reset the controller (register-initiated, CC.EN 1->0;
   the power-cycle/recovery analogue in `fw/nvme_emu_recovery_check.spl` is no
   longer the only option),
   assert post-reset state matches the spec's reset-survival rules for X (queues
   gone, features at default or saved value as applicable).
4. **Fault** — perform X under injected failure: media error via the decaying
   emulator (`nvme_controller_new_emu()`, `fw/nvme_controller.spl:84-87`),
   queue-full/backpressure (`fw/hil_queue_backpressure_check.spl` precedent),
   task-pool exhaustion (`fw/task_pool_fail_closed_check.spl` precedent); assert
   an error SC, SMART/error-log accounting (`error_count`, `media_errors`), and
   no corruption.
5. **Persistence** — perform X, power-cycle without and with a clean checkpoint
   (`dirty_since_checkpoint`, `unsafe_shutdowns`, `fw/nvme_controller.spl:54-57`);
   assert durable effects (Flushed writes, Format result, committed firmware
   slot) survive and `unsafe_shutdowns` accounting is correct.

## What could not be verified in this session

- Any NVMe document text: every class assignment, mandatory-log list, and
  mandatory-FID claim above is MODEL and must be re-checked against lawfully
  acquired current NVM Express documents before any conformance claim. The
  clause ledger `spec/nvme/clauses.sdn` is extracted from a LOCAL copy of Base
  2.3 that is deliberately not in this repository, and carries identifiers and
  generated paraphrases only — never specification prose.
- That a row is `transport level` means only that the command travels the
  host-equivalent path in this Simple host model. It does NOT mean byte-accurate
  Identify/log-page layouts, a linked firmware image, QEMU or board execution,
  or PCIe interoperability. Every generated scenario restates this boundary.
- Whether the plan §6.1 version list (Base 2.4 etc.) is still current.
- Completeness of the mandatory Set/Get Features FID set and Identify CNS set —
  feature names given; the exact required lists are MODEL.
