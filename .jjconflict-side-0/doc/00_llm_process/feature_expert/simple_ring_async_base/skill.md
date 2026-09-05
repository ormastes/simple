# SimpleRing async-base feature expert

## Role

Own the lane knowledge for the SimpleRing/task/profile V1 foundation. This is
an LLM wiki entry, not a shared executable Codex/Claude skill and not authority
to invent a runtime migration. Keep the current pure-Simple evidence separate
from the broader ring-first architecture proposal.

## Current status

The foundation has common value contracts, profile validation/fingerprints, a
bounded hosted `SimpleRing`, a bounded software provider, a hosted mission
admission adapter, and a fixed-capacity trace ring. It is not yet a native
provider ecosystem, executor replacement, compiler lowering, or proven static
mission runtime.

## Ownership and paths

| Concern | Owner/path |
|---|---|
| Ring/task values and validation | `src/lib/common/contracts/execution/simple_ring_async_v1.spl` |
| Profile values, presets, validation, canonical text, fingerprint | `src/lib/common/contracts/execution/async_profile_v1.spl` |
| Fixed-capacity ring storage and lifecycle | `src/lib/nogc_async_mut/async_ring/simple_ring.spl` |
| Software reference provider | `src/lib/nogc_async_mut/async_ring/software_provider.spl` |
| Legacy Future poll adapter | `src/lib/nogc_async_mut/async_ring/future_compat_adapter.spl` |
| Hosted mission admission adapter | `src/lib/nogc_async_mut/async_ring/mission_adapter.spl` |
| Fixed-capacity trace storage | `src/lib/nogc_async_mut_noalloc/async/async_trace_ring.spl` |
| Scalar mission exact-wakeup set | `src/lib/nogc_async_mut_noalloc/async/mission_ready_set.spl` |
| Existing Future compatibility surfaces | `src/lib/nogc_async_mut/async/future.spl`, `src/lib/nogc_async_mut/async_host/future.spl` |
| Existing green/thread/task surfaces | `src/lib/nogc_async_mut/concurrent/cooperative_green.spl`, `src/lib/nogc_async_mut/concurrent/thread.spl`, `src/lib/nogc_async_mut/thread_pool.spl` |
| Ring lifecycle tests | `test/01_unit/lib/nogc_async_mut/async_ring/simple_ring_spec.spl` |
| Contract tests | `test/01_unit/lib/common/contracts/execution/simple_ring_async_v1_spec.spl` |
| Profile tests | `test/01_unit/lib/common/contracts/execution/async_profile_v1_spec.spl` |
| Requirements/design and lane state | `doc/02_requirements/feature/simple_ring_async_base.md`, `doc/04_architecture/simple_ring_async_base.md`, `doc/05_design/simple_ring_async_base.md`, `.spipe/simple-ring-async-base/state.md` |

## Invariants

- Capacity is fixed at construction; full admission is typed and nonblocking.
- A ring has one mutable owner. Wrong-owner mutations are rejected.
- Tokens contain ring identity, slot, and generation; reset/reuse rejects stale
  tokens and cannot wake a reused task.
- Reservation, release, commit, provider take, terminal completion, and
  completion consumption are separate lifecycle transitions.
- A single-shot in-flight operation has one terminal success, failure, or
  cancelled result. Duplicate terminal publication is rejected and counted.
- Completions retain the exact task key; no Future/task-table scan is implied.
- `AsyncTaskFrame`, `TaskContext`, and `TaskPollResult.Pending(token)` are
  explicit value contracts. They do not imply generated compiler frames.
- Profile fingerprints cover the declared V1 configuration. A profile record
  is policy data and validation, not storage or executor construction.

The hosted ring exposes validated operation metadata, typed payload leases,
all-or-nothing batch admission, explicit cancellation state, caller-clock
latency telemetry, and bounded software-provider depth admission. These are
hosted executable mechanisms, not proof of native mapping or link-time-static
mission storage.

## Verification

The focused unit/integration specs cover construction/fullness, owner checks, FIFO index
queues, generation reuse, reset, stale and duplicate completion rejection,
cancellation outcomes, task/context validation, terminal shapes, profile
preset validation, and fingerprint changes. They do not prove scheduler
fairness, native I/O, mission storage, or compiler lowering.

## Blockers and migration boundaries

- Compiler implicit-await insertion and generated frame/MIR lowering are later
  work. The named Future adapter maps one nonblocking legacy `poll` result to
  the canonical result using a caller-supplied admitted token; explicit
  Future/await otherwise remains a compatibility surface.
- Executor integration and native exact-wake ingress remain follow-on work; the
  software provider and system scenario prove the bounded reference path only.
- The hosted mission adapter validates task, operation, buffer, trace, deadline,
  timer, and join/cancellation capacities and reports its proof limits. True
  link-time-static mission pools and compiler-generated task storage remain
  unimplemented. The scalar ready set avoids explicit collection allocation
  and task scanning for up to 64 slots, but enclosing placement is not
  compiler-proven. The trace ring is fixed-capacity but likewise does not claim
  link-time-static placement.
- The performance spec records ring latency/occupancy/batch counters, but no
  admitted pure-Simple baseline, RSS, or allocation receipt exists yet.
- Native `io_uring`, OS/SOSIX/device providers, NVMe, server/DB, render, and
  GPU migrations are provider/conformance lanes below the common contract.
- Existing Future, cooperative-green, multicore-green, pool-task, and
  OS-thread paths may receive additive adapters, but they must retain explicit
  blocking/fallback/ownership/cancellation facts and cannot redefine V1.

## Update rule

Refresh this page when V1 names, owners, focused tests, acceptance status, or a
migration boundary changes. Keep claims tied to executable source and tests.
