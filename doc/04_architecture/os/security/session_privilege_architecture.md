# SimpleOS Session + Sub-Privilege Architecture (decision record)

Status: DESIGN 2026-07-13. Extends `ocap_privilege_architecture.md` with the
session layer. Depth: `doc/01_research/os/security/session_subprivilege_hierarchy_research.md`.
Recon of existing infra (file:line) is authoritative below.

## Decision

Privilege is scoped to a **Session**, and sessions form a **tree where
authority only narrows downward**: `ceiling(child) ⊆ current(parent)`. Session
kinds are first-class:

```
System → Tenant → User → SubRole → Llm
```

Each node has its own capability arena (a CSpace) and resource budget; a node
can only hold caps its parent currently holds, attenuated. This directly gives:
a **user session** (the user's max authority at login), **sub-privileges**
(the user drops authority into a SubRole, irreversibly), and **LLM sessions**
(attenuated, sealed, ephemeral children — the ticketing/scheduling roles).
KEY FINDING: **no new kernel mechanism** — just a `kind` + parent-ceiling
invariant over the EXISTING session arena + `spawn_with_cspace` (Lane P1) +
`pledge` + epoch-bump revoke.

## The five gaps this closes (recon-verified, file:line)

1. **No session grouping** — `TaskCapRecord` (`kernel/ipc/capability.spl:22`)
   has no `session_id`; `CSpace{session_id}` is design-only. → add `session_id`
   to the task cap record; a `Session` owns a set of tasks (a job tree).
2. **User identity never reaches the OS** — sshd hardcodes
   `authenticated_user="root"` (`apps/sshd/ssh_session.spl:603`) and never
   propagates it. → login mints a **UserSession** from a signed, content-
   addressed user policy = the user's max CSpace.
3. **Teardown leaks** — `revoke_all_for_task()` exists
   (`capability.spl:311`) but SSH disconnect (`ssh_session.spl:1055-1104`)
   never calls it; no job-tree kill. → session teardown = DFS over the
   session subtree bumping each arena `epoch` (O(1)/session; caps die on next
   `cap_check`), budget refunded upward.
4. **LLM server unscoped** — `OsMcpServer` (`services/llm/_McpOsServer/
   server_class.spl:65`) is a stateless singleton; every tool is available to
   any client, no per-request identity. → each LLM request runs in an
   **LlmSession** whose CSpace gates which MCP tools resolve; absent cap =
   tool not present (no ambient authority, no probing surface).
5. **Containers unbound** — `IsolationLevel`/`NamespaceRegistry`
   (`scheduler/process_isolation.spl`) are owned by `pid`, not session. →
   a container is a CSpace + budget + label-namespace **owned by exactly one
   session**, epoch-bound to it.

## Data structures (extend the existing Session arena)

```
enum SessionKind { System, Tenant, User, SubRole, Llm }
Session {
  id: u64, kind: SessionKind, epoch: u32,      # epoch bump = O(1) bulk revoke
  principal: Principal,                          # who this acts for
  ceiling: RightsCeiling,                        # max this session may ever hold
  current: CapabilitySet,                        # what it holds now (⊆ ceiling)
  budget: ResourceBudget,                         # cgroup analogue
  parent: u64, children: [u64],                   # the tree
  sealed: bool,                                    # Capsicum-style: no new ambient
}
# INVARIANT (enforced at spawn/delegate): ceiling(child) ⊆ current(parent)
```

## Lifecycle (thin monotone layers over existing primitives)

- **login(principal) → UserSession**: verify signed user policy → build the
  user's max CSpace → new Session{kind:User, ceiling=current=maxcaps}.
  Concurrent GUI + SSH logins get independent sessions/arenas (macOS model).
  Wire at `ssh_session.spl:603` (replace the hardcoded root with the
  authenticated principal → session).
- **open_subrole(mask) → SubRole**: apply an irreversible `pledge` (AND-mask)
  on a child's `current`; never re-widen. Regain authority only via a fresh
  login. (Reuses existing `pledge`, `capability.spl:270`.)
- **spawn_llm(role_grants) → LlmSession**: `spawn_with_cspace` (Lane P1)
  wrapped as a SEALED, ephemeral (Qubes-DispVM-style) child; grants resolved
  from the PARENT session's `current` arena, not the user's max. The
  ticketing vs scheduling roles are two LlmSessions off the same image_hash.
- **teardown(session)**: DFS the subtree, bump each `epoch`, refund budget up,
  emit a lineage audit record. Hook this into `ssh_session.spl:1055` so
  disconnect actually revokes. (Reuses existing generation/epoch revoke.)

## Container cowork

A container = the §container-as-cspace shape (CSpace + budget + label
namespace), owned by one session, epoch-bound. Cross-session cowork (the
"scheduler-LLM asks ticketing-LLM to create a ticket") = a **single-use escrow
cap** minted into the RECEIVER's arena via the broker — not shared ambient
state. Many tenants → many users → many sessions → many containers, all with
disjoint arenas and quotas; teardown is per-node.

## Broker (control plane only)

A per-user broker (systemd `user@.service` / Fuchsia `session_manager` /
Capsicum Casper / powerbox analogue) holds the spawn/attenuate authority and
mints single-use caps on explicit user designation. It has NO data-plane
access — it cannot read the resources it brokers, only hand out attenuated
caps. This is where `OsMcpServer` evolves: from a singleton tool dispatcher to
a per-session broker that resolves tools against the requesting LlmSession's
CSpace.

## Phased plan (builds on OCap P1–P4)

- **S1** `session_id` on TaskCapRecord + a `Session` table; `login` mints a
  UserSession; propagate principal from sshd. Gate (seed-run): two logins get
  disjoint sessions; a task's caps are session-scoped.
- **S2** `open_subrole` (irreversible pledge on a child) + the
  `ceiling(child) ⊆ current(parent)` invariant enforced at spawn. Gate: a
  subrole cannot regain a dropped cap; cannot exceed parent.
- **S3** teardown hook into SSH disconnect → epoch-bump revoke of the session
  subtree + budget refund. Gate: disconnect revokes all session caps; child
  tasks die.
- **S4** LlmSession = spawn_llm over P1; OsMcpServer resolves tools per
  session CSpace. Gate: ticketing-LLM's tool set excludes calendar; scheduling
  excludes tickets; same image_hash. (This is the user's headline scenario.)
- **S5** containers owned by sessions; cross-session single-use escrow caps.
  Gate: cross-LLM ticket creation via escrow, revoked at task end.
- **S6** multi-tenant System→Tenant→User tree; disjoint arenas/quota.

Gates S1–S4 are seed-run-verifiable (the session/cap logic is pure-Simple
kernel .spl); full in-kernel enforcement at boot is toolchain-gated. Depends on
Lane P1 (`spawn_with_cspace`) landing first.
