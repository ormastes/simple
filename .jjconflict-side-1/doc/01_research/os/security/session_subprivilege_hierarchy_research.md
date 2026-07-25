# Session + Hierarchical Sub-Privilege Design for SimpleOS

Status: RESEARCH 2026-07-13. Extends the landed object-capability design with a
first-class **Session** hierarchy: user sessions, LLM sessions, and sub-role
sessions, with authority that only *shrinks* down the tree. Reads-first:

- `doc/04_architecture/os/security/ocap_privilege_architecture.md` (decision record)
- `doc/01_research/os/security/capability_revocation_attenuation_research.md`
  — esp. **§C SESSION SEPARATION** and **§D.4/§D.5** (session arenas, `Session`
  struct, `cap_check`).
- `doc/01_research/os/security/llm_role_cspace_container_design.md`
  — esp. **§3.1** (`CSpace{session_id}`), **§3.2** (`spawn_with_cspace`,
  `AttenuationSpec`), **§3.4** (sealed mode / pledge), **§3.6** (container =
  shape of C-Space), **§3.8** (orchestration lifecycle).
- `doc/01_research/os/security/privilege_ocap_sota_research.md` (seL4/Fuchsia/
  Genode/CHERI substrate).

The substrate already exists: `CapabilityToken{kind, generation, owner,
token_id, parent_token_id, depth}`, `revoke_transitive`, monotonic
`AttenuationSpec`, per-object generation counters, kernel `Gate` objects, and
**session arenas** (`Session{id, epoch, arena, cap_quota, parent}`). This doc
does **not** re-derive the cap machinery; it adds the *session taxonomy and the
login-to-LLM authority-flow* on top of it.

## 0. The gap this closes

The landed design has exactly one notion of "session": an arena of cap-table
slots with an epoch, tagged onto a `CSpace` via `session_id`. That is the
*mechanism*. It has no *policy taxonomy*: no distinction between "a human logged
in" and "an LLM task the human spawned", no notion of a user's **maximum**
authority vs a **reduced** operating mode, and no rule that a spawned child's
ceiling is bounded by its parent session's *current* (not maximum) authority.

The three requirements:

1. **User session vs LLM session as distinct first-class kinds.** Login mints a
   `UserSession` holding the user's authority. The user spawns `LlmSession`s as
   *children* holding an attenuated subset (never more). LLM sessions are the
   ticketing/scheduling role instances from the existing design, now with a
   parent and a lifetime bound to it.
2. **Users with sub-privileges.** A user's authority is itself hierarchical: a
   **max** privilege set, plus a reduced **sub-privilege** operating mode (the
   inverse of `sudo` — *drop*, never gain), and the ability to create
   sub-roles/sub-sessions under themselves. Nested attenuation
   `user → sub-role → LLM-task`; authority only narrows going down.
3. **Container cowork.** A container is a *shape* of C-Space (§3.6): CSpace +
   budget + label-namespace. A session **owns** containers; containers attach to
   exactly one session and die with it. Multi-tenant: many users, each with
   sessions, each with LLM sub-sessions and containers, all quota-accounted.

The unifying idea, drawn from Genode and Fuchsia: **the session IS the unit of
authority accounting and the unit of teardown.** The cap table already gives
O(1) teardown by epoch; this doc gives that epoch a *place in a tree* and a
*kind*.

---

# Part I — External research (mechanism + mapping to a capability OS)

## 1. systemd-logind — the Linux session/scope/slice/per-user-manager tree

**Mechanism.** `systemd-logind` builds a three-level cgroup hierarchy per login
([DeepWiki: user & session mgmt](https://deepwiki.com/systemd/systemd/6-user-and-session-management),
[user@.service(5)](https://www.freedesktop.org/software/systemd/man/latest/user@.service.html)):

```
user.slice                     # all human users
└─ user-1000.slice             # ONE user (UID 1000) — the "UserSession root"
   ├─ user@1000.service        # the PER-USER service manager (systemd --user)
   │  └─ app.slice/…           # user's long-lived services, spawned BY the user mgr
   ├─ session-4.scope          # GUI login (gdm)      — one interactive login
   └─ session-19.scope         # SSH login            — another interactive login
```

Two spawn origins: processes started by the per-user manager land in
`user@UID.service`; processes started by a login agent (sshd, gdm) land in a
`session-N.scope`. **Cgroup delegation** is the key rule
([systemd.io CGROUP_DELEGATION](https://systemd.io/CGROUP_DELEGATION/)):
`Delegate=yes` is permitted **only on scope and service units, never on slice
units**, because slices are inner tree nodes and delegation would create two
writers (systemd + the delegatee) under the single-writer rule. So a *leaf*
session may sub-partition its own budget, but an inner grouping node may not.

**Map to a cap OS.** `user.slice → user-UID.slice → {user@.service,
session-N.scope}` maps almost 1:1 to a **Session tree**: a per-tenant root, a
per-user `UserSession`, a per-user **session broker** (`user@.service`), and
per-login **interactive sub-sessions** (`session-N.scope`). The single-writer
delegation rule becomes: **only leaf sessions carry a live `CSpace` and may
spawn/attenuate**; inner sessions are pure quota-and-teardown grouping nodes
(they own an `arena` + `cap_quota` but no runnable task). `ResourceBudget`
(§3.1) is the `cpu.max`/`memory.max`/`pids.max` of the slice, charged
hierarchically. The lesson to copy: **budget and authority live in the same
tree; a parent node caps the sum of its children.**

## 2. Fuchsia session framework + component framework — the closest model

**Mechanism.** In Fuchsia, *everything is a component*, and a component plus its
children form a **realm**; the whole system is one **component instance tree**
([Fuchsia components intro](https://fuchsia.dev/fuchsia-src/concepts/components/v2/introduction),
[Understanding Fuchsia Security](https://arxiv.org/pdf/2108.04183)). A newly
created program **has no authority at all — not even to allocate memory**; its
parent must *route* every capability to it. **Capability routing is the access
control**: a capability must be explicitly declared in a route from provider to
consumer, and *by choosing which routes exist, a parent defines the sandbox of
each child* ([original principles](https://fuchsia.dev/fuchsia-src/contribute/contributing-to-cf/original_principles)).

The **session framework** ([RFC-0092 Sessions](https://fuchsia.dev/fuchsia-src/contribute/governance/rfcs/0092_sessions))
adds a `session_manager` component that is the **parent of the session**. The
*session* is itself a component (hence a realm) that "encapsulates the product's
user experience". `session_manager` holds a bundle of capabilities (storage,
network, hardware protocols) and **offers a subset of them to the session**; the
session in turn routes sub-subsets to its own children. `session_manager` can
start, stop, and restart the session, and exposes debug protocols to drive it.
Teardown uses the underlying **job tree**: all processes live in a rooted tree
of *jobs*, `zx_task_kill(job)` terminates every process beneath it, and job
policy is **restrict-only down the tree** — a child can never widen authority
([Zircon concepts](https://fuchsia.dev/fuchsia-src/concepts/kernel/concepts)).

**Map to a cap OS.** This is the design target almost verbatim:
`session_manager` = the **per-user session broker**; a **session = a realm =
a Session node whose CSpace is a strict subset of its parent's**; capability
routing = the `CapGrantSpec` recipe of `spawn_with_cspace` (§3.2); "no authority
at birth" = "empty pouch by default" (arch gap 1). An `LlmSession` is just a
**child realm** whose routed capability set is an attenuated slice of the user's.
The restrict-only-down-the-tree job policy is exactly the nested-attenuation
invariant (Part II §14). We keep Fuchsia's separation of *broker* (privileged,
routes caps) from *session* (holds only what was routed).

## 3. Qubes OS — domains as sessions, DisposableVMs as ephemeral LLM tasks

**Mechanism.** Qubes isolates by Xen domain
([arch spec 0.3](https://www.qubes-os.org/attachment/doc/arch-spec-0.3.pdf),
[glossary](https://doc.qubes-os.org/en/r4.3/user/reference/glossary.html)).
**dom0** is the trusted admin domain: *no network*, minimal VM-facing surface,
exists only to launch/manage domains (`qvm-create/-run/-ls/-remove`). **AppVMs**
run user apps; an AppVM **borrows its root filesystem from a template** (shared,
read-only) and owns only its `/home` and user files — a *copy-on-write template*
model. **DisposableVMs** are lightweight VMs created on demand to host a single
app (open one untrusted file), and **destroyed when closed**
([disposables](https://doc.qubes-os.org/en/latest/user/how-to-guides/how-to-use-disposables.html)).

**Map to a cap OS.** dom0's "no network, only manages domains" = the **session
broker / init** should hold *management* authority (spawn, revoke, budget) but
*no data-plane* authority — it can mint an `LlmSession` but cannot itself read
the user's calendar. AppVM's "template rootfs + private home" = an immutable
content-addressed role image (§3.5) + a per-instance writable scratch container.
**DisposableVM = the canonical `LlmSession`**: minted for one task, holds a
minimal attenuated pouch, and is **torn down on completion** (epoch bump) — the
right default lifetime for an LLM instance handling untrusted prompt input.

## 4. Android — multi-user, work profiles, per-app UID sandbox

**Mechanism.** Android assigns each app a unique UID and runs it in its own
process with its own PID/mount/net/user namespaces; the kernel enforces the
**Application Sandbox** at the process level, hardened by SELinux MAC
([app sandbox](https://source.android.com/docs/security/app-sandbox),
[Android Platform Security Model](https://arxiv.org/pdf/1904.05572)).
**Multi-user**: secondary users get isolated app data and settings but can share
already-installed app *binaries* (data isolated, code shared). A **work
(managed) profile** is a partial user: it requires trusting a profile-owner app
to activate and is "less strict than full user isolation" — a *delegated
sub-domain* within one physical user, administered by a policy controller.

**Map to a cap OS.** Three nested isolation tiers map to three Session kinds:
physical user → `UserSession`; managed/work profile → **`SubRoleSession`** (a
reduced, policy-owned sub-domain the user carves out of themselves); per-app UID
sandbox → the per-instance `CSpace` container (§3.6). Android's "share the binary,
isolate the data" is precisely the SimpleOS invariant *role behavior =
f(image_hash, cspace)*: one immutable image, per-session pouch. The work-profile
"profile owner" is the **broker** that administers the sub-session's ceiling.

## 5. macOS — security sessions, audit sessions, per-session keychains

**Mechanism.** On login the Security layer creates a **security session** with a
unique ID (maintained by `securityd`); later this was re-based on the
kernel-level **audit session** (ASID)
([Apple: Sessions](https://developer.apple.com/documentation/security/sessions),
[AuthSession.h](https://github.com/st3fan/osx-10.9/blob/master/Security-55471/libsecurity_authorization/lib/AuthSession.h),
[audit vs security session](https://developer.apple.com/forums/thread/132875)).
Crucially, **keychain unlock state is per-login-session**: unlocking the keychain
in a GUI session does *not* carry into an SSH session — secrets are scoped to the
session that authenticated for them, preventing remote exfiltration.

**Map to a cap OS.** Two lessons. (a) A session has a **stable kernel-assigned
id** distinct from any process — SimpleOS already has `Session.id`; secrets and
credentials should be **caps owned by a session's arena**, not by a process or a
user globally. (b) **Per-session secret scoping**: a credential cap (keychain
analogue) minted into the GUI `UserSession`'s arena is *not visible* to a
separately-authenticated SSH `UserSession` for the same human — because they are
different session arenas. This directly informs multi-login: the same human may
hold two concurrent `UserSession`s (GUI + SSH) that do **not** share unlocked
secret caps; an `LlmSession` inherits only the credential facets its parent
session explicitly routes.

## 6. Capsicum — capability mode, process descriptors, Casper broker

**Mechanism.** `cap_enter(2)` puts a process into **capability mode**: access to
*global OS namespaces* (filesystem, PID) is cut off; only rights referenced by
already-held file descriptors (themselves narrowable via `cap_rights_limit`) work
([Capsicum for FreeBSD](https://www.cl.cam.ac.uk/research/security/capsicum/freebsd.html),
[Capsicum paper](https://research.google.com/pubs/archive/36736.pdf)).
`pdfork(2)` returns a **process descriptor** (an FD) instead of a PID, so a child
is named by an unforgeable, delegable handle rather than a global integer, and
`pdkill`/`pdwait` operate on the FD
([process descriptors](http://lackingrhoticity.blogspot.com/2010/10/process-descriptors-in-freebsd-capsicum.html)).
**Casper** is a broker daemon: it forks *before* the app enters capability mode,
keeps ambient authority, and a sandboxed app that needs a global operation (DNS,
open-by-path) **delegates the request to Casper** over IPC
([Capsicum Update 2019](https://freebsdfoundation.org/wp-content/uploads/2019/11/Capsicum-Update-2019.pdf)).

**Map to a cap OS.** `cap_enter` = `CSpace.sealed` (§3.4), but **default-on and
set by the spawner/manifest**, not opt-in by the app (Capsicum's retrofit
lesson). A process descriptor = the **task-cap in slot 0** and the parent's
**child-session handle** — killing a child session is `pdkill` on its handle, not
a PID lookup. Casper = the **broker/powerbox slot**: a sealed `LlmSession` that
needs a legitimately-global operation sends a *request* (data, not authority) up
its `slot 1` parent endpoint, and the broker either proxies or mints a single-use
cap (§3.8). Nested sandboxing (Casper sub-sandboxes its own services) = sessions
nest arbitrarily deep, each sealed.

## 7. seL4 CSpace subtrees + Genode session-as-IPC-primitive

**seL4.** A thread's TCB points at its **CSpace** (root CNode); syscalls name
caps relative to it. A "session" = a freshly built CSpace; teardown = revoke +
delete the root CNode, and *deleting the last cap to a CNode deletes the caps it
contains* — cascading subtree teardown, cost O(session caps)
([seL4 capabilities tutorial](https://docs.sel4.systems/Tutorials/capabilities.html)).
This is the *structural* teardown model; SimpleOS's arena-epoch bump is the O(1)
*logical* version of it (§D.4), with lazy structural reclaim.

**Genode — sessions ARE the IPC primitive (most relevant).** Every service
relationship is a **session**, created *through the parent*, labeled with the
client identity, and **funded by a client-provided RAM + capability quota**
([capability-based security](https://genode.org/documentation/genode-foundations/20.05/architecture/Capability-based_security.html),
[resource trading](https://genode.org/documentation/genode-foundations/25.05/architecture/Resource_trading.html),
[recursive system structure](https://genode.org/documentation/genode-foundations/22.05/architecture/Recursive_system_structure.html)).
A parent, on a child's session request, may **(a) deny, (b) delegate to its own
parent, (c) implement the service locally, or (d) route to another child** — a
four-way policy decision at every parent-child edge. When the session's RPC
object is destructed, **the kernel invalidates its capability, implicitly
revoking every delegated copy**. The system is a **recursive tree**: a node with
sub-nodes is the parent; the parent creates children *out of its own resources*
and defines their execution environment.

**Map to a cap OS.** Genode is the blueprint for the *hierarchy*: (1) sessions
are created **through the parent**, so the parent mediates and can attenuate —
this is `spawn_with_cspace` where the child's grants are resolved from the
*caller's* CSpace (§3.2 step 4). (2) **Client-provided quota** = hierarchical
`ResourceBudget` charged against the parent (§3.2 step 3); a session cannot
exhaust the global table. (3) The **four-way parent policy** (deny / escalate to
grandparent / serve locally / route sideways) is exactly the broker's decision
menu when an `LlmSession` asks for authority it lacks (§3.8 proxy-vs-grant, now
generalized). (4) **Object-death = implicit revoke** = arena epoch bump. Genode
proves the model scales to a whole OS as *nothing but* nested sessions.

## 8. Login / PAM / SSH session lifecycle

**Mechanism.** PAM splits a login into phases; **`pam_open_session`** runs
*after* authentication and credential-setting to perform session setup (utmp/wtmp
entry, start ssh-agent, set env), and **`pam_close_session`** performs teardown
(remove utmp entry, SIGTERM the agent)
([pam_open_session](https://pubs.opengroup.org/onlinepubs/8392999799/pam_open_session.htm),
[pam_ssh(8)](https://manpages.ubuntu.com/manpages/focal/man8/pam_ssh.8.html)).
Open and close **may be called by different processes** (login opens, init
closes). SSH multiplexing (`ControlMaster`) lets many interactive channels share
one authenticated transport — many *interactive* sessions under one *login*.

**Map to a cap OS.** The PAM open/close bracket = the **UserSession
mint/teardown** bracket, and the "different process closes it" property is why
teardown must be a **kernel session-epoch bump keyed on `Session.id`**, not a
process-lifetime hook — any authorized holder of the session's control cap can
close it. `pam_setcred` before `pam_open_session` = the login broker mints the
user's **credential caps** into the fresh arena *before* any task runs.
SSH-multiplexed channels = multiple **interactive sub-sessions** under one
`UserSession` (the `session-N.scope` analogue of §1), each its own leaf arena.

## 9. Powerbox / POLA broker — granting sub-authority on demand

**Mechanism.** In CapDesk/Polaris the **powerbox** is a trusted UI process
holding broad authority; when an app needs a file, the powerbox shows the file
dialog, and *the user's act of designation* (picking the file) is what grants the
app authority to exactly that one file — authority is inferred from designation,
not pre-granted
([Plash powerbox](http://plash.beasts.org/powerbox.html),
[Polaris](https://www.researchgate.net/publication/220425548_Polaris_Virus-safe_computing_for_Windows_XP),
[awesome-ocap](https://github.com/dckc/awesome-ocap)). This is POLA applied
interactively: apps start with *nothing* and gain single-object authority per
user action.

**Map to a cap OS.** The **session broker is a powerbox.** An `LlmSession`
starts empty; when it needs (say) write to one specific ticket, it does *not*
hold a tickets cap — it requests, and the broker, on a user-approved or
policy-approved designation, mints a **single-use attenuated cap** (`CSLOT_
SINGLE_USE`, §3.7) for that one object. "Designation = authority" is enforced
structurally: the LLM can only name objects via caps it was handed, so a
prompt-injection cannot *ask* for something it was never designated (no ambient
namespace to probe — §3.4). The powerbox is the human-in-the-loop or
policy-in-the-loop escalation path that keeps standing authority minimal.

## 10. Comparison

| System | "Session" unit | Hierarchy | Attenuation rule | Teardown | Broker |
|---|---|---|---|---|---|
| systemd-logind | scope/slice | user.slice → user-UID → scope | budget caps sum | cgroup kill | `user@.service` |
| Fuchsia | session component = realm | component instance tree | route-only-down, restrict-only | `zx_task_kill(job)` | `session_manager` |
| Qubes | domain (VM) | dom0 → AppVM → DispVM | policy in dom0 | destroy VM (DispVM auto) | dom0 |
| Android | user / profile / app-UID | user → work-profile → app | SELinux MAC + UID | user/profile removal | profile owner |
| macOS | security/audit session | login → session | per-session secret scope | session close | `securityd` |
| Capsicum | process in cap-mode | pdfork tree | `cap_rights_limit` monotone | `pdkill` FD | Casper |
| seL4 | CSpace (root CNode) | CDT | Mint ≤ parent rights | delete root CNode | (none / manual) |
| **Genode** | **session (IPC primitive)** | **recursive component tree** | **parent mediates, quota-funded** | **RPC-object death revokes** | **the parent** |
| Powerbox | app authority grant | user → powerbox → app | designation = authority | drop granted cap | powerbox UI |
| **SimpleOS (this)** | **Session arena + kind** | **tenant → user → sub-role → llm** | **monotone ceiling down-tree** | **epoch-bump cascade** | **session broker** |

The synthesis: take **Genode's session-is-everything hierarchy + quota**,
**Fuchsia's realm/broker split + route-only-down**, **Capsicum's default-sealed +
Casper broker**, **Qubes' ephemeral disposable = LLM instance**, **macOS
per-session secrets**, and **powerbox on-demand designation** — all expressible
on the *existing* cap table by adding a **kind** and a **parent-ceiling
invariant** to `Session`.

---

# Part II — The SimpleOS Session + sub-privilege design

## 11. Session kinds — the taxonomy

A `Session` gains a **kind** and a **principal**. Four kinds, forming a strict
tree in which authority only narrows downward:

```text
SessionKind:
  System   # kind 0: the root broker/init domain. Holds MintAuthority.
           #   Data-plane authority = NONE (Qubes dom0 rule). One per boot.
  Tenant   # kind 1: a multi-tenant partition (org / customer). Inner node:
           #   quota + teardown grouping, no runnable task. Optional (single-
           #   tenant boxes skip it: User parents directly to System).
  User     # kind 2: a human's authenticated login. Minted at login with the
           #   user's MAX CSpace (§12). Inner-ish: owns the per-user broker.
  SubRole  # kind 3: a REDUCED operating mode the user carves under themselves
           #   (sudo-inverse / work-profile / pledged shell). Leaf-or-inner.
  Llm      # kind 4: an LLM task instance = the ticketing/scheduling role.
           #   Always a leaf; ephemeral by default (Qubes DispVM).
```

The tree shape (single-tenant collapse in parens):

```text
System (root, MintAuthority, no data caps)
└─ [Tenant "acme"]                         # optional multi-tenant layer
   └─ UserSession "alice" (max CSpace)     # minted at login (§12)
      ├─ per-user Broker (Casper/user@.service/session_manager analogue)
      ├─ SubRoleSession "alice/deploy"     # pledged-down sub-privilege (§13)
      │  └─ LlmSession "deploy-llm" (⊆ deploy)   # attenuated child (§14)
      ├─ InteractiveSubSession "ssh-3"     # a login channel (PAM/scope analogue)
      └─ LlmSession "calendar-scheduler" (⊆ alice)   # attenuated child
         └─ (single-use tickets cap via broker powerbox, §17)
```

**Invariant (the whole point):** for any session `S` with parent `P`,
`ceiling(S) ⊆ current(P)` — a child's *maximum* authority is bounded by the
parent's *current* authority (not the parent's max). Because sub-privilege drop
(§13) shrinks `current(P)`, any child spawned afterward is bounded by the reduced
set. This is Fuchsia's route-only-down + seL4's Mint-≤-parent, made a session
property.

## 12. Data structures (extending the landed `Session`)

Extend the `Session` of the revocation doc §D.5 (kept fields unchanged; new
fields appended so the existing `cap_check` is untouched):

```text
struct Principal:                 # who this session acts for
    kind:      u8                 # USER | ROLE | LLM | SYSTEM
    user_id:   u32                # 0 for System; the human/tenant principal
    role_hash: [u8; 32]           # LlmSession: the immutable image hash (§3.5)
    label:     text               # "alice", "alice/deploy", "calendar-scheduler"

struct Session:                   # EXTENDS revocation §D.5
    id:         u16               # (existing) kernel-assigned, process-independent
    epoch:      u32               # (existing) bump => all session caps logically dead
    arena:      SlotRange         # (existing) contiguous cap-table slots
    cap_quota:  u32               # (existing) Genode-style accountable budget
    parent:     u16               # (existing) tree edge; kill cascades to children
    # --- new ---
    kind:       u8                # SessionKind (§11)
    principal:  Principal
    ceiling:    RightsCeiling     # the MAX authority this session may ever wield
    current:    RightsCeiling     # <= ceiling; sub-privilege drop lowers this (§13)
    budget:     ResourceBudget    # cgroup analogue (§3.1); charged from parent
    control:    u32               # slot of the session-control cap (close/spawn/attenuate)
    first_child: u16              # intrusive child list (0 = none)
    next_sib:    u16              # sibling link; O(children) DFS on teardown
    flags:      u32               # SESS_SEALED | SESS_EPHEMERAL | SESS_LEAF_ONLY
                                  #   | SESS_NO_DATAPLANE (System/broker) | SESS_PLEDGED

struct RightsCeiling:             # the authority envelope, not individual caps
    label_prefixes: [text]        # allowed cap labels ("mem.calendar", "ipc.tickets")
    rights_cap:     u32           # global rights ceiling AND-ed into every mint here
    fs_prefix:      text          # path-prefix ceiling for any FileRead/Write mint
    can_spawn:      bool          # may this session create child sessions at all
    can_mint_root:  bool          # holds MintAuthority (System only, normally)
    max_child_depth:u8            # remaining session-nesting budget (monotone -1/level)
```

`RightsCeiling` is an **envelope**, distinct from the concrete cap slots in the
arena: it is the *policy bound* checked when this session tries to **mint or
delegate** a cap, whereas the per-slot `rights` / `Gate` machinery bounds a cap
already held. Both must pass. A session can hold *fewer* caps than its ceiling
allows (it just hasn't asked); it can never mint one *outside* the ceiling.

A tiny kernel `session_table: [Session; MAX_SESSIONS]` (MAX_SESSIONS ~4096,
`u16` id) is the only place the tree lives. Sessions are few (one per login /
sub-role / LLM task), so a full DFS over the subtree at teardown is cheap — the
*caps* are many (handled by the O(1) epoch), the *sessions* are not.

## 13. Sub-privilege drop — irreversible pledge within a session

A user does **not** gain privilege (there is no `sudo` up-escalation; authority
is never ambient to reacquire). Instead the user **drops** into a reduced mode by
opening a `SubRoleSession` whose `current` is a pledged-down subset — OpenBSD
`pledge`, generalized to the session envelope, and **irreversible for the session
lifetime** (the existing `pledge()` = self-applied AND-mask, already monotone,
revocation doc §D.5 note 4).

```text
fn open_subrole(parent: SessionId, drop: PledgeSpec) -> Result<SessionId>:
    P = session_table[parent]
    require P.current.can_spawn and P.kind in {User, SubRole}
    # NEW ceiling = parent.current INTERSECT the pledge (monotone; kernel rejects
    # any field that would WIDEN — EPERM, the seL4-Mint rule):
    c = RightsCeiling {
        label_prefixes: intersect(P.current.label_prefixes, drop.keep_labels),
        rights_cap:     P.current.rights_cap & drop.keep_rights,
        fs_prefix:      extend_only(P.current.fs_prefix, drop.narrow_fs),
        can_spawn:      P.current.can_spawn and drop.allow_spawn,
        can_mint_root:  false,                       # sub-roles NEVER mint root
        max_child_depth: P.current.max_child_depth - 1,
    }
    S = new_session(kind=SubRole, parent, ceiling=c, current=c,
                    budget = charge(P.budget, drop.budget),   # <= parent remaining
                    flags = P.flags | SESS_PLEDGED
                            | (drop.seal ? SESS_SEALED : 0))
    # Grants into the sub-role's arena are re-delegated from P's arena (depth-1,
    # attenuated, §3.2 step 4). The sub-role starts with an EMPTY pouch and pulls
    # only the facets the pledge kept.
    return S.id
```

Properties: (1) **Irreversible** — there is no `raise_privilege`; to regain
authority the human authenticates a *new* `UserSession` (a new login), never
re-widens a live one (macOS per-session secrets + OpenBSD pledge). (2) **Nested**
— a `SubRoleSession` can itself `open_subrole`, each strictly narrower, bounded
by `max_child_depth`. (3) **The `current` field is what children see** — an
`LlmSession` spawned under a pledged sub-role inherits the reduced `current`, not
the user's max `ceiling`. Example: `alice` (max = fs:/home/alice + calendar rw +
tickets w + net) opens `alice/deploy` pledging `keep = {fs:/home/alice/proj,
net}`; any LLM she now spawns under `deploy` *cannot* touch her calendar or
tickets — the authority was dropped before the child existed.

## 14. UserSession mint at login

Login is the PAM `authenticate → setcred → open_session` bracket (§8), performed
by the **System broker** (the only holder of `MintAuthority`):

```text
fn login(cred: Credential) -> Result<SessionId>:            # runs in System session
    u = authenticate(cred)                                  # PAM auth phase; -> user_id
    require u.ok
    # 1. Determine the user's MAX authority from the signed user policy record
    #    (content-addressed, like a RoleManifest but for a human principal):
    pol = load_user_policy(u.user_id)     # SDN, signed; the user's ceiling of record
    ceiling = pol.max_ceiling             # RightsCeiling: labels/fs/rights/net the human may EVER hold
    # 2. Mint the UserSession arena under the tenant (or System if single-tenant)
    parent = tenant_of(u.user_id)         # Tenant session, or System
    S = new_session(kind=User, parent,
                    principal = Principal{USER, u.user_id, label: u.name},
                    ceiling = intersect(ceiling, session_table[parent].current),
                    current = same,                 # starts at full personal max
                    budget  = charge(parent.budget, pol.budget),
                    flags   = 0)                    # NOT sealed: the user is trusted
    # 3. setcred: mint the user's credential caps INTO S.arena (macOS keychain:
    #    per-session, NOT shared with a concurrent SSH UserSession for same human)
    for c in pol.credentials: mint_into(S.arena, c)  # secret store, home fs cap, etc.
    # 4. open_session: start the per-user Broker (Casper/user@.service analogue)
    #    as a child task in S with SESS_NO_DATAPLANE-style limited control caps.
    spawn_broker(S)
    return S.id
```

Key points: the user's **max CSpace = `pol.max_ceiling`**, loaded from a *signed,
content-addressed* user policy (not editable by the user's own tasks — the
role-escape defense of §3.5 applied to humans). Concurrent logins (GUI + SSH) for
the same human mint **independent `UserSession`s with independent arenas** — they
do not share unlocked-secret caps (macOS lesson §5). The `UserSession` itself is
*not* sealed (the human is the trust root of their own subtree), but every child
it spawns can be.

## 15. LlmSession spawn as an attenuated child

An `LlmSession` is `spawn_with_cspace` (§3.2) wrapped so the child is a *session*,
not just a task — it gets its own arena/epoch/ceiling and a parent edge, so it
tears down as a unit and is bounded by the parent's `current`:

```text
fn spawn_llm(parent: SessionId, role: RoleManifest, grants: [CapGrantSpec],
             budget: ResourceBudget, ephemeral: bool) -> Result<SessionId>:
    P = session_table[parent]
    require P.current.can_spawn and P.current.max_child_depth > 0
    verify_image(role.image)                       # hash + signature, §3.5
    # ceiling of the LLM session = parent.current INTERSECT manifest ask (monotone):
    c = intersect_ceiling(P.current, role_ceiling(role))
    S = new_session(kind=Llm, parent,
                    principal = Principal{LLM, P.principal.user_id, role.image.hash, role.role_name},
                    ceiling = c, current = c,
                    budget  = charge(P.budget, budget),        # hierarchical, <= parent
                    flags   = SESS_SEALED                      # default-on (Capsicum §6)
                            | (ephemeral ? SESS_EPHEMERAL : 0)
                            | SESS_LEAF_ONLY)                  # LLMs don't spawn sub-roles
    # Resolve EACH grant from the PARENT session's arena (not the user's max),
    # re-delegate depth-1 with AttenuationSpec, reject any non-monotone spec (EPERM):
    for g in grants:
        require g.attenuation within c                 # ceiling check
        src = slot_lookup(P, g.source)                 # from PARENT's CSpace
        tok = delegate(src, g.attenuation)             # existing CapabilityManager.delegate
        install(S.arena, g.dst_slot, tok, g.label, g.flags)
    load_and_start(S, role.image)                      # SIP or ring-3 lane per isolation
    return S.id
```

This *is* the ticketing-vs-scheduling demo of the arch doc P1, now with a
parent session: **same immutable image, different pouch**, and the pouch is
resolved from the parent session's *current* arena — so a scheduler LLM spawned
under a pledged sub-role literally cannot be handed a tickets cap the sub-role
dropped. `SESS_EPHEMERAL` is the Qubes DispVM default: the session self-tears at
task completion.

## 16. Session hierarchy teardown — epoch-bump cascade

Teardown of any session kills its entire subtree, using the existing per-session
epoch (revocation §D.4) walked over the small session tree:

```text
fn teardown(sid: SessionId, reason: u32):
    # DFS the session subtree (few nodes); bump each epoch => all caps in each
    # arena are logically dead on the NEXT cap_check (O(1) per session):
    for S in dfs_post_order(sid):        # children before parent
        S.epoch += 1                     # instant logical revoke of S.arena's caps
        # gates owned by S die because their backing slots' session epoch changed;
        # cross-session escrow gates (§17) were minted in the RECEIVER's arena, so
        # they die with the RECEIVER, never leaking authority out of a dead session.
        refund(parent_of(S).budget, S.budget)          # return quota up the tree
        audit_log(S.principal, S.arena.lineage, reason) # parent_token_id provenance
        mark_arena_reclaimable(S.arena)                 # lazy sweep, EROS-eager on hot
    unlink_from_parent(sid)
```

Why bump *every* session in the subtree rather than only the root: each session
has its own `epoch`, and `cap_check` reads `sessions[s.session].epoch`
(revocation §D.5) — a child cap references the *child's* session id, so the child
epoch must move. Sessions are few, so the DFS is cheap; the expensive part (the
caps) stays O(1) per arena. Triggers: explicit close (PAM `close_session`, any
holder of `S.control`), parent teardown (cascade), anomaly (prompt-injection
detector / budget-exceed / deadline on an `SESS_EPHEMERAL` LLM). The
`parent_token_id` chain in each arena is a complete "who could do what" audit
record, logged at teardown.

**Alternative considered (ancestor-epoch check):** make `cap_check` walk the
parent chain verifying each ancestor's epoch, so a single root bump suffices
lazily. Rejected as default: it adds per-*use* cost to the hot path for a
per-*teardown* saving, and teardown is already cheap (few sessions). Kept as a
fallback if session fan-out ever grows large.

## 17. Containers attach to sessions

A container is **not a new object** — it is the §3.6 *shape* of a `CSpace`
(slots = visible-object namespace, budget = cgroup analogue, sealed+lane =
boundary strength). The extension: **a container is always owned by exactly one
session** and inherits that session's epoch, so it dies with the session.

```text
Container := ( CSpace.slots     — namespace of visible objects
             , CSpace.budget    — sub-budget charged from the owning session
             , CSpace.sealed+lane — boundary strength )
attach:  every CSpace.session_id points at the owning Session.id (existing field).
         A session may own MANY containers (e.g. one per task it runs); each is a
         sub-arena, quota-charged from the session's budget, epoch = session.epoch.
```

- **Session owns/runs containers.** An `LlmSession` typically owns one container
  (the role's `CSpace`). A `UserSession` owns many (the broker, each interactive
  shell, each spawned app). Teardown of the session bumps the epoch that all its
  containers' slots reference → all containers die together (Fuchsia realm kill).
- **Cross-container / cross-session cowork** uses the §3.7 escrow pattern: a
  single-use attenuated cap moved into the *receiver's* arena (so it is bound to
  the receiver's session epoch, never the sender's) — the powerbox grant (§9).
  The broker's four-way Genode policy (deny / escalate / serve-locally / route)
  decides each request.
- **Budget nesting** is the systemd single-writer rule (§1): a container's
  `ResourceBudget` is charged from its session's `budget`, which is charged from
  the parent session's — `cpu.max`/`memory.max`/`pids.max` summed up the tree,
  enforced at the existing scheduler/allocator/endpoint hooks (§3.6).

## 18. The session broker (per-user manager / powerbox)

Each `UserSession` spawns a **broker** child (the `user@.service` /
`session_manager` / Casper / powerbox synthesis). It is the *only* component in
the user's subtree that:

- Holds the user's `control` caps to *spawn* sub-sessions and LLM sessions and to
  *attenuate* (it routes, like Fuchsia `session_manager`); but carries
  `SESS_NO_DATAPLANE` — it can mint a calendar cap into an LLM child from the
  user's arena, yet is configured to hold no live calendar cap of its own
  (Qubes dom0: manage, don't touch data).
- Answers a sealed child's request for global/ambient operations (name
  resolution, spawn-a-subrole) — the Casper delegation path — and mints
  **single-use attenuated caps on user/policy designation** (the powerbox: the
  child never holds standing authority; each grant is one act of designation).
- Implements the Genode four-way decision at the parent edge: deny / escalate to
  the System broker / serve locally / route to a sibling container.

Because the broker is itself a session-child, a compromised broker is bounded by
*its* ceiling and revoked by the same epoch bump — no ambient super-authority
sits below the human.

## 19. Multi-user and multi-tenant

```text
System (root broker, MintAuthority, no data caps)          # one per boot
├─ Tenant "acme"  (quota partition; inner node, no task)
│  ├─ UserSession "acme/alice"  (max CSpace_A)  ── Broker_A
│  │  ├─ SubRole "alice/deploy" ── LlmSession "deploy-llm" (⊆ deploy)
│  │  └─ LlmSession "alice/scheduler" (⊆ alice)  ⇄ single-use tickets via Broker_A
│  └─ UserSession "acme/bob"    (max CSpace_B)  ── Broker_B   # arenas disjoint from alice
└─ Tenant "globex"
   └─ UserSession "globex/carol" (max CSpace_C) ── Broker_C
```

- **Isolation between tenants/users is structural**, not by ACL: disjoint
  arenas, disjoint ceilings, disjoint budgets. `alice` cannot name any object
  `bob` holds because designation is by cap and no cross-arena cap exists unless
  a common ancestor (Tenant/System broker) explicitly escrows one.
- **Quota fairness** is Genode resource-trading up the tree: `Tenant "acme"` has
  a fixed `cap_quota` + `ResourceBudget`; `alice` + `bob` sessions draw from it;
  one user cannot exhaust another's or the tenant's neighbor's resources.
- **Teardown is per-node**: closing `alice`'s login epoch-bumps her subtree
  (all her sub-roles, LLM sessions, containers) and refunds her budget to
  `Tenant "acme"`; `bob` is untouched. Tearing down `Tenant "acme"` cascades to
  all its users (customer offboarding).
- **The same human, two logins** = two sibling `UserSession`s with the same
  `user_id` but independent arenas/secrets (macOS §5) — SSH and GUI do not share
  unlocked credentials; an LLM under one cannot reach the other's caps.

## 20. Lifecycle summary

```text
LOGIN     System.broker.login(cred) -> UserSession S_u  (max ceiling, creds minted, broker up)
DROP      S_u.open_subrole(pledge)  -> SubRole S_r      (current shrinks; irreversible)
SPAWN     S_r.spawn_llm(role, grants, ephemeral=true) -> LlmSession S_l  (sealed, ⊆ S_r.current)
RUN       S_l runs immutable image; requests up slot-1 to Broker; powerbox mints single-use caps
COWORK    scheduler S_l ── request ──> Broker ── escrow single-use ticket cap ──> ticketing S_l'
REVOKE    anomaly/timeout: teardown(S_l)   (epoch bump; ephemeral auto on task end)
LOGOUT    teardown(S_u)  -> DFS bumps S_r, S_l, all containers; budget refunded to Tenant; audit
```

## 21. Mapping to existing files / phases

- Extend `Session` + add `session_table` in the kernel cap layer alongside the
  revocation-doc §D.5 migration (`capability.spl` → arena ranges). `SessionKind`,
  `Principal`, `RightsCeiling` are new types in `src/os/kernel/ipc/`.
- `login`, `open_subrole`, `spawn_llm`, `teardown` are thin policy layers over the
  **existing** `spawn_with_cspace` / `CapabilityManager.delegate` / `pledge` /
  epoch-bump primitives — no new kernel mechanism, only the tree/kind/ceiling
  bookkeeping and the monotone checks.
- Broker = a userland component (`src/os/userlib/` or a service) holding the
  `control` caps; not kernel code.
- Fits the arch doc phases: this is **P4 (Container = CSpace + budget +
  namespace)** generalized to sessions, layered on **P1 spawn_with_cspace** and
  the revocation **D.4 session arenas**. No change to P5/P6 lanes — sessions are
  arch-neutral (the CHERI/SIP/MMU floor only changes wall thickness, not the
  tree).

## 22. Verification gates (spec tests)

1. **Ceiling monotonicity:** `open_subrole` / `spawn_llm` with a widening
   `AttenuationSpec` or out-of-ceiling label → `EPERM`. Property test over random
   pledge chains: `current(child) ⊆ current(parent)` always.
2. **Drop-before-spawn:** user drops calendar in a sub-role, then spawns an LLM;
   the LLM's `cap_stat` scan shows no calendar slot and a calendar op faults.
3. **Teardown cascade:** kill a `UserSession`; every descendant session's caps
   fail `cap_check` (epoch) on the next use; budget refunded exactly; no
   cross-session escrow cap survives in a *dead* sender.
4. **Tenant isolation:** `alice` cannot resolve or use any `bob` cap; quota
   exhaustion by `alice` does not starve `bob`.
5. **Ephemeral LLM:** an `SESS_EPHEMERAL` LLM session self-tears at task
   completion / deadline; re-run mints a fresh arena (no state carryover — Qubes
   DispVM).
6. **Per-session secrets:** two concurrent logins for one human do not share an
   unlocked-secret cap (macOS invariant).

## 23. Open questions / risks

- **Ancestor-epoch vs subtree-DFS teardown** (§16): DFS chosen; revisit if
  session fan-out per user grows into the thousands.
- **Broker trust:** the per-user broker holds spawn/attenuate control caps; it is
  bounded by its ceiling and revocable, but a compromised broker can mis-route
  within the user's *current* envelope. Mitigation: `SESS_NO_DATAPLANE` + minimal
  control ceiling + audit of every mint. Consider a language-verified broker
  image (SIP lane) so its routing logic is compiler-checked.
- **Human policy record editing:** `load_user_policy` must be signed and
  content-addressed (§14) or a user task could widen its own ceiling — the
  role-escape defense (§3.5) applied to humans; needs an admin-only signing path.
- **Interactive sub-session granularity:** whether each SSH-multiplexed channel is
  its own leaf session (clean teardown) or shares one — mirrors the systemd
  scope-per-login question (§1); default = one leaf session per channel.
- **Cross-tenant escrow policy:** the System broker *can* escrow a cap between
  tenants; needs an explicit, audited, default-deny policy so multi-tenancy stays
  structurally isolated.

---

## Sources (indexed via web search; summaries cited inline)

- **systemd-logind:** [CGROUP_DELEGATION](https://systemd.io/CGROUP_DELEGATION/) ·
  [user@.service(5)](https://www.freedesktop.org/software/systemd/man/latest/user@.service.html) ·
  [DeepWiki: user & session management](https://deepwiki.com/systemd/systemd/6-user-and-session-management)
- **Fuchsia:** [RFC-0092 Sessions](https://fuchsia.dev/fuchsia-src/contribute/governance/rfcs/0092_sessions) ·
  [Components v2 introduction](https://fuchsia.dev/fuchsia-src/concepts/components/v2/introduction) ·
  [Original principles (capability routing / no ambient authority)](https://fuchsia.dev/fuchsia-src/contribute/contributing-to-cf/original_principles) ·
  [Understanding Fuchsia Security (arXiv)](https://arxiv.org/pdf/2108.04183) ·
  [Zircon concepts (job tree)](https://fuchsia.dev/fuchsia-src/concepts/kernel/concepts)
- **Qubes OS:** [Architecture spec 0.3](https://www.qubes-os.org/attachment/doc/arch-spec-0.3.pdf) ·
  [Disposables](https://doc.qubes-os.org/en/latest/user/how-to-guides/how-to-use-disposables.html) ·
  [Glossary](https://doc.qubes-os.org/en/r4.3/user/reference/glossary.html)
- **Android:** [Application Sandbox](https://source.android.com/docs/security/app-sandbox) ·
  [The Android Platform Security Model (arXiv)](https://arxiv.org/pdf/1904.05572)
- **macOS:** [Apple Developer: Sessions](https://developer.apple.com/documentation/security/sessions) ·
  [AuthSession.h](https://github.com/st3fan/osx-10.9/blob/master/Security-55471/libsecurity_authorization/lib/AuthSession.h) ·
  [Audit vs security sessions](https://developer.apple.com/forums/thread/132875)
- **Capsicum:** [Capsicum for FreeBSD (Cambridge)](https://www.cl.cam.ac.uk/research/security/capsicum/freebsd.html) ·
  [Capsicum paper (Google)](https://research.google.com/pubs/archive/36736.pdf) ·
  [Process descriptors](http://lackingrhoticity.blogspot.com/2010/10/process-descriptors-in-freebsd-capsicum.html) ·
  [Capsicum Update 2019 (Casper)](https://freebsdfoundation.org/wp-content/uploads/2019/11/Capsicum-Update-2019.pdf)
- **Genode:** [Capability-based security](https://genode.org/documentation/genode-foundations/20.05/architecture/Capability-based_security.html) ·
  [Recursive system structure](https://genode.org/documentation/genode-foundations/22.05/architecture/Recursive_system_structure.html) ·
  [Resource trading](https://genode.org/documentation/genode-foundations/25.05/architecture/Resource_trading.html) ·
  [Inter-component communication](https://genode.org/documentation/genode-foundations/19.05/architecture/Inter-component_communication.html)
- **seL4:** [Capabilities tutorial (CSpace subtree teardown)](https://docs.sel4.systems/Tutorials/capabilities.html)
- **PAM / SSH sessions:** [pam_open_session (Open Group)](https://pubs.opengroup.org/onlinepubs/8392999799/pam_open_session.htm) ·
  [pam_ssh(8)](https://manpages.ubuntu.com/manpages/focal/man8/pam_ssh.8.html)
- **Powerbox / POLA:** [Plash powerbox](http://plash.beasts.org/powerbox.html) ·
  [Polaris: virus-safe computing](https://www.researchgate.net/publication/220425548_Polaris_Virus-safe_computing_for_Windows_XP) ·
  [awesome-ocap](https://github.com/dckc/awesome-ocap)
