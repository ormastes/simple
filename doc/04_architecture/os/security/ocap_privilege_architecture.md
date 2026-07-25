# SimpleOS Object-Capability Privilege Architecture (decision record)

Status: DESIGN 2026-07-13. Synthesizes three research docs into the chosen
model + phased plan. Depth references:
`doc/01_research/os/security/privilege_ocap_sota_research.md`,
`.../capability_revocation_attenuation_research.md`,
`.../llm_role_cspace_container_design.md`.

## Decision

SimpleOS adopts a **pure object-capability (OCap) model** — permission is an
unforgeable token held by a *task/instance*, never an ambient property of a
*user*. Identity-based DAC/RBAC is rejected (fails the "same binary, different
privilege per role" requirement). This is the perfect fit for the driving use
case: one immutable `llm_worker` binary, spawned as a ticketing role
(write-only ticket IPC cap) or a scheduling role (rw calendar cap), where the
role is *entirely* the injected capability pouch.

## The hybrid enforcement floor (one API, three backends)

SimpleOS **owns its compiler and language**, so it can enforce capabilities at
the lowest floor each target allows, behind ONE capability API:

| Target | Enforcement floor | Cost of a cap-mediated call |
|---|---|---|
| Compiler-verified Simple image | **Language-based** (SIP-style): compiler proves memory safety + import allowlist → run in the shared ring-0 address space | ~function call (Singularity: <5% overhead, ~1k-cycle IPC) |
| CHERI-RISC-V (future) | **Hardware** fat-pointers, monotonic narrowing in silicon | intra-AS domain crossing ≈ call |
| Commodity x86/ARM, or foreign code | **MMU** per-process C-Space (today's ring-3 path) | syscall + context switch |

Same `spawn_with_cspace()` call everywhere; the floor drops as low as the
target permits. Compiler-verified images get SASOS speed; untrusted/foreign
code falls back to MMU isolation — no API change.

## What SimpleOS already has (recon, file:line)

Substantial OCap substrate exists — this is *completion*, not greenfield:
- `CapabilityToken{kind, generation, owner, token_id, parent_token_id, depth}`
  (`kernel/types/capability_types.spl:22`) — delegation lineage + depth budget.
- `CapabilityManager` grant/revoke/**revoke_transitive**(CDT-style ancestry
  cascade)/pledge/unveil + `capability_kind_allows()` monotonic attenuation
  (path-prefix, device class, extent range, rights mask);
  `CapabilitySet` = the C-Space (`kernel/ipc/capability.spl`).
- Two-gate `PrivilegeMask` (kernel-call/IRQ/IO bitmasks); `GrantTable.safecopy`
  (page-table-validated memory grants).
- L4 IPC with a `CapTransfer` flag; per-PID `IsolationLevel`.

## The four gaps this architecture closes

1. **No per-instance C-Space injection** — `_handle_spawn` uses
   `CapabilitySet.full()` (`syscall_process.spl:139`); fork inherits verbatim.
   → **`spawn_with_cspace(SpawnSpec{image_hash, grants[], isolation, budget})`**
   with monotonic `AttenuationSpec`; fork = inherit-attenuated, never full. A
   grep guard forbids new `CapabilitySet.full()` call sites.
2. **CapTransfer is a stub** — fill with move+attenuate semantics over
   `IpcHeader.cap_count` (≤2-cap inline fast path); single-use slots for the
   "scheduler-LLM hands ticketing-LLM a one-shot create-ticket cap" flow.
3. **Compiler proves effects, not caps** — add a `--profile=sealed-role`
   WIT-world-style import allowlist so a role that lacks a cap *fails to
   compile* (the language-based floor).
4. **IsolationLevel is advisory** — make it derived/validated from the
   C-Space + `ResourceBudget`, gated at the syscall entry, not a hint.

## Core data structures

```
CSpace { sealed: bool, slots: [Slot; 64], budget: ResourceBudget, session_id: u64 }
Slot   { token: CapabilityToken, slot_gen: u32 }        # userspace handle = (slot, slot_gen): u64
                                                        # two gen layers: slot reuse + token revoke
Container = CSpace + ResourceBudget(cgroup analogue) + label-namespace of visible objects
Session   = a CSpace arena; O(1) teardown bumps the arena generation → bulk revoke
```

Handle injection ABI (dependency injection — the app is dumb/stateless, no
hardcoded paths): well-known slots 0=self, 1=parent/orchestrator endpoint,
2=log, 3+=role pouch; delivered via an `AT_SIMPLE_CSPACE` auxv manifest page
(extends `_build_sysv_stack_frame`); app reads `caps.get("label")` → absent =
`nil` (no probing surface for prompt-injection escalation).

## Revocation (layered, from the research)

- **Generation counter** (exists): O(1) bulk revoke of all caps derived from a
  token — the cheap default; also the session-arena teardown primitive.
- **Caretaker/redirector object**: for *selective* per-recipient revoke — hand
  a proxy cap, revoke by killing the proxy (one indirection).
- **`revoke_transitive`** (exists): recursive CDT revoke of a delegation subtree.
- **Compiler/type-enforced monotonic attenuation** in user space (membrane
  pattern): narrowing needs no kernel round-trip.

## Immutable roles

blake3 content-addressed `/store` (write-once) + signed `RoleManifest` (SDN,
extends `capability_set_from_sandbox_lowering`). Role behavior = f(image_hash,
cspace) — no mutable on-disk config, so a compromised role cannot escalate by
rewriting its own config; its authority is exactly its injected pouch.

## Phased plan (maps to existing files)

- **P1** `spawn_with_cspace` + `AttenuationSpec`, kill the `full()` ambient
  hole, fork inherit-attenuated. Gate: ticketing-vs-scheduling same-binary
  demo — ticketing instance faults on FS write; scheduling instance faults on
  ticket write. Host-verifiable via seed-run.
- **P2** CapTransfer runtime over L4 IPC (move+attenuate, single-use slots).
  Gate: cross-instance one-shot ticket grant.
- **P3** `--profile=sealed-role` compiler import allowlist (language floor).
  Gate: a role using an un-granted cap fails to compile.
- **P4** Container = CSpace + budget + label-namespace; IsolationLevel
  derived+syscall-gated. Gate: budget/namespace enforced, not advisory.
- **P5** SIP lane — compiler-verified images co-located in one address space
  (SASOS), MMU fallback for foreign code. Gate: IPC cycle-count vs ring-3.
- **P6** CHERI-RISC-V hardware-capability backend (long-term; riscv64 target).

## Cross-arch

The capability API is arch-neutral; only the *floor* differs (§hybrid). P1–P4
run on every current arch (x86/arm/riscv, MMU floor). P5 SASOS is arch-neutral
Simple. P6 CHERI is riscv-first. Per the standing cross-arch requirement, each
phase states coverage; P6 is explicitly riscv-only until Morello/ARM CHERI.
