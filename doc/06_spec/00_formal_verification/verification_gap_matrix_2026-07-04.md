# Formal Verification Gap Matrix — 2026-07-04

Mission-critical runtime bar (seL4 / SPARK-Ada standard): every safety-critical
runtime mechanism has a machine-checked model with zero trust bypasses.

## How verification is gated (honesty model)

All Lean 4 (v4.30.0) Lake projects under `src/verification/` are auto-discovered
and built by:

```bash
sh scripts/check/check-lean-proofs.shs                 # all projects + std proofs
sh scripts/check/check-lean-proofs.shs --project src/verification/<domain>
```

The gate **fails closed**: after stripping comments it rejects any `sorry`,
`admit`, `axiom`, `constant`, `opaque`, `unsafe`, `set_option autoImplicit true`,
or `set_option maxHeartbeats 0`. A `sorry` can NEVER count as green — it fails
the project. Consequence: partially-proved models cannot be landed as Lake
projects; open obligations are recorded in this document instead (see "Open
obligations" below), never as admitted lemmas.

## Sorry / axiom census (2026-07-04)

- Real `sorry`/`admit` in `src/verification/**/*.lean`: **0**
  (9 grep hits are all doc comments of the form "zero sorry" / "without sorry").
- `axiom` declarations: **0**.
- Gate self-test: `sh scripts/check/check-lean-proofs.shs --self-test`.

## Inventory (24 Lake projects, theorem counts)

| Domain | Theorems | What is proved |
|---|---|---|
| memory_model_drf | 90 | DRF definition sound; conflict table; unordered write/read + lock acquire/release races are NOT DRF (active parallel stream) |
| kernel_scheduler | 80 | park/unpark/complete safety, double-complete, enqueue/tick progress, work-steal threshold, resource pool bounds |
| memory_capabilities | 66 | capability lattice (shared/exclusive/isolated): downgrades allowed, upgrades denied; aliasing-xor-mutability access policy |
| actor_channel | 52 | FIFO per sender, no-lost-message (send/close/recv-park), close wakes all, backpressure no-overflow, dispatch-error no-halt |
| riscv_product | 39 | RVFI/SBY profile coverage (parallel stream) |
| kernel_capabilities | 38 | capability derivation/revocation invariants |
| formal/nvfs | 33 | NVFS state machine: publish-root, recovery-replay-requires-commit, EOC terminal |
| db_storage | 33 | MVCC visibility, recovery, storage invariants |
| type_inference_compile | 27 | inference determinism, async effect soundness, promise wrap/unwrap |
| manual_pointer_borrow | 23 | borrow-state machine: exclusive xor shared, take/release round-trips |
| gc_boundary | 18 | tier inference monotone/sound, noalloc closure, copy isolation counterexample |
| gc_manual_borrow | 17 | collect is no-op on borrowed, borrow pins across collect |
| fat32 | 16 | chain-link validity, bad-marker rejection |
| **thread_lifecycle** (NEW) | 14 | join/detach soundness — see below |
| aop_weaver | 13 | weave model |
| **type_value_semantics** (NEW) | 10 | struct=value / class=ref — see below |
| visibility_export | 10 | private-child not exported |
| ui_compositor | 10 | damage-rect retention |
| **gc_reachability** (NEW) | 9 | tri-color safety — see below |
| tensor_dimensions | 7 | shape safety |
| macro_auto_import | 7 | auto-import requires macro |
| module_resolution | 5 | resolution determinism |
| nogc_compile | 3 | nogc append split |
| async_compile | 3 | async lowering |

Plus `src/compiler_rust/lib/std/src` (std proofs project, same gate).

## Gap matrix

| Area | Status | Where | Criticality |
|---|---|---|---|
| THREADS: lifecycle, join/detach | **COVERED (NEW)** | `thread_lifecycle` — result write-once, exactly-once join delivery, no double-join, detach/join mutual exclusion, wf preservation | P0 |
| THREADS: DRF / happens-before | COVERED | `memory_model_drf` (90 thm; parallel stream actively extending) | P0 |
| THREADS: TLS isolation | MISSING — propose: per-thread store independence (write to T1's slot invisible to T2) | — | P2 |
| PROCESS: spawn/exit/wait, zombie-freedom | MISSING — propose: process table machine; every exited pid is waited or reparented; no wait on live pid returns | — | P1 |
| PROCESS: signal safety | MISSING | — | P2 |
| GC: boundary/tier inference | COVERED | `gc_boundary` | P0 |
| GC: borrow pinning across collect | COVERED | `gc_manual_borrow` (+ parallel stream: collection keeps borrows live) | P0 |
| GC: tri-color invariant preservation | **COVERED (NEW)** | `gc_reachability.markStep_preserves_invariant` | P0 |
| GC: no-dangling-after-collect | **COVERED (NEW)** | `gc_reachability.no_dangling_after_sweep` | P0 |
| GC: mark completeness (reachable ⇒ black, termination) | **OPEN obligation** — safety direction proved; completeness needs worklist termination measure | documented here, NOT admitted as sorry | P1 |
| GC: root-set completeness vs real runtime root enumeration | **OPEN obligation** — requires model of stack-map/registers | documented here | P1 |
| MEMORY MODEL: aliasing xor mutability | COVERED | `manual_pointer_borrow`, `memory_capabilities` (+ stream: shared-blocks-exclusive) | P0 |
| SCHEDULER: per-tick progress | COVERED | `kernel_scheduler` (+ stream: enqueue-tick progress, two-tick actor progress) | P0 |
| SCHEDULER: global fairness / starvation-freedom | PARTIAL — steal threshold + progress proved; no long-run fairness theorem | `kernel_scheduler` | P1 |
| CHANNELS/ACTORS: no-lost-message | COVERED | `actor_channel.no_lost_task_*` | P0 |
| CHANNELS/ACTORS: no-double-receive | COVERED | `actor_channel.recv_advances_tail`, `process_one_at_most_one` | P0 |
| LOCKS: acquire/release ordering races | COVERED | `memory_model_drf` lock theorems (parallel stream) | P0 |
| TYPE SYSTEM: struct=value, class=ref soundness | **COVERED (NEW)** | `type_value_semantics` — copy independence both directions, alias write visibility | P0 |
| TYPE SYSTEM: inference determinism, async effects | COVERED | `type_inference_compile` | P1 |
| FFI: rt_* contract safety (arg/ownership across boundary) | MISSING — propose: model rt_* call as capability transfer; no callee retention of caller-owned nogc pointers | — | P1 |
| FILESYSTEM | COVERED | `fat32`, `formal/nvfs` | P1 |
| KERNEL: capabilities | COVERED | `kernel_capabilities`, `memory_capabilities` | P0 |
| HARDWARE: RISC-V RVFI | COVERED | `riscv_product` (stream) | P1 |

Summary: **17 covered** (4 newly landed this pass), **1 partial**, **4 missing**
(P1: process lifecycle, FFI contract; P2: TLS, signals), **2 open obligations**
inside otherwise-green GC domains (documented above, never sorry-admitted).

## Items created this pass (all zero-sorry, build verified)

1. `src/verification/type_value_semantics/` — 10 theorems.
   Key: `struct_copy_independent`, `struct_source_mut_preserves_copy`,
   `class_alias_write_visible`, `struct_distinct_identity`.
2. `src/verification/gc_reachability/` — 9 theorems.
   Key: `markStep_preserves_invariant` (strong tri-color: no black→white
   survives a mark step), `no_dangling_after_sweep`, `sweep_reclaims_white`,
   `sweep_keeps_live`.
3. `src/verification/thread_lifecycle/` — 14 theorems.
   Key: `no_double_join`, `detach_excludes_join`, `join_excludes_detach`,
   `finish_write_once`, `join_finished_yields_value`, four `*_preserves_wf`.

## How to verify

```bash
sh scripts/check/check-lean-proofs.shs   # full sweep; PASS requires build + 0 bypasses
sh scripts/check/check-lean-proofs.shs --project src/verification/thread_lifecycle
sh scripts/check/check-lean-proofs.shs --project src/verification/gc_reachability
sh scripts/check/check-lean-proofs.shs --project src/verification/type_value_semantics
grep -rn '\bsorry\b' src/verification --include='*.lean'   # comment-only mentions expected
```

## Coordination note

A parallel session is actively landing `verification: prove ...` commits on
`memory_model_drf` (lock-order races), `kernel_scheduler`/`actor_channel`
(tick progress), `gc_manual_borrow`, `riscv_product`, `db_storage`,
`ui_compositor`, `fat32`, `visibility_export`, `macro_auto_import`,
`nogc_compile`. Those rows are listed as covered above; do not duplicate.
Next priorities after this pass: process lifecycle model (P1), FFI rt_*
contract model (P1), GC mark completeness + root-set completeness (P1),
scheduler starvation-freedom (P1).
