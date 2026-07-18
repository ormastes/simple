# Capability Revocation and Attenuation — Deep External Research

**Date:** 2026-07-13
**Scope:** The two hardest problems in capability-based OS design — revocation
("the ultimate challenge") and attenuation — surveyed across seL4, KeyKOS,
EROS, CHERI, Fuchsia/Zircon, Genode, and the OCap-language tradition (E, Pony),
ending in a concrete recommended design for SimpleOS.
**Local baseline:** SimpleOS already ships generation-counter capability tokens
(`src/os/kernel/ipc/capability.spl`: `CapabilityManager` with a global
`next_generation: u64`, per-task `CapabilitySet` lists, grant/revoke by
generation bump). This document evaluates that as the baseline and designs the
missing layers on top of it.

---

## 0. Why revocation is the hard problem

A capability bundles *designation* (which object) with *authority* (what you
may do to it) in an unforgeable token. Delegation is then trivially cheap —
just copy the token — which is exactly why taking authority *back* is hard:
the grantor no longer knows where all the copies are. Every real system picks
a point on a triangle of costs:

1. **Pay on revoke** — walk/sweep to find and kill every copy (seL4 CDT,
   CHERI sweeps).
2. **Pay on use** — validate a liveness fact on every access (generation
   counters, EROS allocation counts, caretaker indirection).
3. **Pay in structure** — constrain where copies can live so they are
   enumerable (C-lists in kernel memory, session arenas, membranes).

Attenuation is the dual problem: *weakening* before delegating. It is cheap
precisely when it can be done without asking the kernel (CHERI monotonic
narrowing, OCap wrappers) and expensive when every derivation is a syscall.

---

## A. REVOCATION — five mechanism families

### A.1 Generation counters / epoch validation (the SimpleOS baseline)

**Mechanism.** Each token embeds a generation number; the authoritative record
(kernel table / object header) holds the current generation. On every use the
kernel compares them; revoke = bump the counter, which lazily invalidates every
outstanding copy. EROS uses exactly this shape at its core: capabilities ("keys")
carry an **allocation count** matched against the object's on-disk/in-core
header, so destroying an object and reusing its frame invalidates all stale keys
without ever finding them ([EROS: a fast capability system, SOSP'99](https://flint.cs.yale.edu/cs428/doc/eros.pdf)).
A 2022 survey/proposal paper classifies this family as "marking-phase only"
revocation and confirms its near-**O(1)** revoke complexity
([A Simple and Efficient Object-Capability Revocation Method, ACM ITCC 2022](https://dl.acm.org/doi/fullHtml/10.1145/3548636.3548656)).

**Costs and properties.**
- Revoke latency: O(1), no traversal, no allocation.
- Use-time cost: one extra load + compare per access (already paid in SimpleOS).
- Kernel entry: validation happens where the authority is checked anyway; the
  bump itself is one kernel write.
- Persistence: trivial — the counter is part of the object record; EROS shows
  it survives a single-level-store checkpoint unchanged.

**What it CANNOT do (the baseline's ceiling):**
1. **All-or-nothing granularity.** Bumping the generation kills *every*
   outstanding token derived from that record at once. There is no
   "revoke only what I gave to task B" without giving B a *different record*,
   which is precisely the caretaker pattern (A.2).
2. **No derivation knowledge.** The kernel cannot answer "who still holds
   authority over X?" — no audit, no selective cascade, no
   revoke-my-delegatees-but-not-me.
3. **Global-counter smell.** SimpleOS's single `next_generation` is a
   correctness-adequate but contention-prone and information-leaking design
   (token values reveal global grant ordering). Per-object counters are
   strictly better and enable O(1) *per-object* bulk revoke.
4. **List-scan revoke.** The current `revoke()` walks per-task arrays; the
   validity check should instead be a table-indexed compare so revoke cost
   does not scale with caps held.

### A.2 Indirection / caretaker / redirector objects (Redell 1974; KeyKOS)

**Mechanism.** Never hand out the real capability. Hand out a capability to a
small proxy (*caretaker*, *revoker*, *front-end*, *redirector*) that you
control and that forwards invocations to the real object. Revoke = destroy or
switch off the proxy. Redell described this in 1974 with "revoker
capabilities" that redirect the access path; it was implemented in CAP-III and
is the canonical selective-revocation pattern
([ACM ITCC 2022 survey](https://dl.acm.org/doi/fullHtml/10.1145/3548636.3548656)).
Norm Hardy's cap-lore notes the key structural condition: the indirection must
itself be *named and controlled by a capability*, and any object invoked by
message can be made indirect by a normal intervening object
([Capability Indirection, cap-lore](http://www.cap-lore.com/CapTheory/Segregate.html)).
KeyKOS built system services this way for 15+ years of production use
([The KeyKOS Nanokernel Architecture](https://css.csail.mit.edu/6.5660/2017/readings/keykos.pdf)).

**Costs and properties.**
- Granularity: **per-recipient** (one caretaker per grantee) or per-purpose
  (one caretaker per contract). This is the only classical pattern that gives
  *selective* revocation.
- Latency of revoke: O(1) — flip the caretaker's alive bit / delete one object.
- Use-time cost: **one extra indirection per access.** In-kernel (a redirector
  slot) this is a pointer chase; in userland (a proxy server) it is a full
  extra IPC hop — the expensive variant.
- Kernel entry: forwarding through a same-process language-level caretaker
  needs none; an OS-level caretaker adds one.
- Leak hazard: a naive caretaker forwards *results* unwrapped — anything the
  object returns (a sub-capability!) escapes the revocation boundary. Fixing
  this transitively is the membrane pattern (§B.3).
- Chains: caretakers compose (A revokes B's view; B re-lends to C through its
  own caretaker); depth = added latency, so kernels should flatten or bound it.

### A.3 seL4: revoke() over the Capability Derivation Tree (CDT)

**Mechanism.** seL4 tracks every capability copy/derivation in a **capability
derivation tree**. Each capability lives in a **CTE** (capability table entry)
= `{ cap, mdbNode }`, where the mdbNode carries a pair of prev/next pointers
forming a **doubly-linked list** (the "mapping database", MDB) that stores the
CDT in preorder with depth information — tree-as-list, two words of overhead
per slot ([Refinement in the formal verification of seL4](https://trustworthy.systems/publications/nicta_full_text/3087.pdf),
[seL4 manual](https://sel4.systems/Info/Docs/seL4-manual-latest.pdf)).
`seL4_CNode_Revoke(cap)` runs `cteRevoke`: repeatedly find the next CDT child
of the slot, delete it, continue until no children remain — with a
**preemption point after each deletion** so a huge revoke cannot destroy
latency guarantees ([seL4 Haskell spec, CNode.lhs](https://github.com/NICTA/seL4/blob/master/haskell/src/SEL4/Object/CNode.lhs)).
Revocation is how a server "restores sole authority" to a shared object and
how an untyped-memory manager reclaims memory for retyping
([seL4 capabilities tutorial](https://docs.sel4.systems/Tutorials/capabilities.html)).

**Revocable vs irrevocable delegation.** Only *children* are revoked. seL4
distinguishes **original** capabilities from **derived** ones: a `Copy`/`Mint`
produces a child; a badged endpoint cap minted from an original is itself
"treated as an original capability and supports one level of derived children"
([cspace.tex, seL4 manual source](https://github.com/seL4/seL4/blob/master/manual/parts/cspace.tex)).
So the grantor chooses at delegation time whether the grantee's copy sits
below them (revocable) or beside them (irrevocable — e.g., resource-manager
handoff where the new owner must be safe from the old one).

**Costs and properties.**
- Granularity: **subtree** — exactly "everything derived from this slot,"
  which is finer than generation-bump (per-derivation, not per-object) but
  coarser than caretaker (cannot skip one child and keep another below it).
- Latency: **O(#descendants)**, unbounded, preemptible; a revoke can also
  cascade object destruction (deleting the last cap to a CNode/TCB deletes the
  caps it contains).
- Kernel entry: always; both delegation (kernel copies between CSpaces) and
  revocation are syscalls.
- Space: 2 pointers + depth bits per capability slot, paid always.
- Persistence: none (seL4 is not persistent); systems that checkpoint would
  have to serialize the MDB list.

### A.4 EROS: allocation counts + back-pointers (keyrings) + persistence

EROS refined the KeyKOS design on commodity hardware and is the instructive
hybrid ([EROS SOSP'99](https://flint.cs.yale.edu/cs428/doc/eros.pdf),
[EROS IEEE overview](https://flint.cs.yale.edu/cs428/doc/eros-ieee.pdf)):

- **Lazy path (disk form):** keys carry allocation counts — generation
  validation, as in A.1. Nothing to sweep on destroy; stale keys die on next
  *prepare* (first use).
- **Eager path (core form):** when a key is *prepared* (converted to a direct
  in-memory pointer for speed), it is threaded onto a per-object circular
  back-pointer chain. Destroying the object walks
  this chain to deprepare/invalidate exactly the prepared keys, and uses
  *depend table* entries to shoot down hardware page-table entries derived
  from those keys. This is mark-and-sweep **bounded to the prepared set**, not
  the whole capability graph.
- **Persistence:** the whole machine image is checkpointed (~consistent
  snapshot, <100 ms marking on a 486; asynchronous writeback). Because
  capabilities live in kernel-interpreted **nodes/capability pages**, the
  capability graph and its allocation counts persist and revocation state
  survives reboot for free — the single-level store makes "revocation is
  durable" a non-feature.

**Lesson:** generation-check on the slow path + back-pointer chains on the
cached fast path is the classic way to get O(1) logical revoke *and* eager
teardown of hot state (page tables, prepared pointers).

### A.5 Hardware: CHERI revocation — CHERIvoke and Cornucopia

CHERI capabilities live in *user registers and user memory* (tagged), so no
table exists to consult: revocation must **find the capabilities themselves**,
garbage-collector style.

- **CHERIvoke** (MICRO'19) established the cost model: freed memory goes to a
  **quarantine**; a **shadow bitmap** (painted at word granularity) marks
  quarantined addresses; when quarantine fills, a **sweep of all memory**
  clears the tag of every capability pointing into painted regions; only then
  is memory reused. Sweep frequency ∝ (memory freed / quarantine size); with a
  **25% heap-size overhead** the average execution overhead is **under 5%**
  (~4.7%), dominated by sweep bandwidth — sweeping runs near DRAM streaming
  speed and is "predictable and describable mathematically"
  ([CHERIvoke paper](https://www.cl.cam.ac.uk/research/security/ctsrd/pdfs/201910micro-cheri-temporal-safety.pdf)).
- **Cornucopia** (IEEE S&P'20) implemented it for real in CheriBSD: the VM
  subsystem tracks capability flow (capability-dirty pages), and a
  **concurrent kernel-resident revocation service** sweeps in the background —
  average overhead **<2%**, worst case 8.9% on SPEC
  ([Cornucopia](https://www.cl.cam.ac.uk/research/security/ctsrd/pdfs/2020oakland-cornucopia.pdf)).
- **Cornucopia Reloaded** (ASPLOS'24) replaced stop-the-world phases with a
  **load barrier** (check-on-load of capabilities from swept pages), the same
  trick concurrent GCs use
  ([Cornucopia Reloaded](https://www.cl.cam.ac.uk/research/security/ctsrd/pdfs/202404asplos-cornucopia-reloaded.pdf));
  follow-ons (PICASSO's colored capabilities, PoisonCap, CHERI-D) attack sweep
  frequency and quarantine size
  ([PICASSO](https://arxiv.org/pdf/2602.09131), [PoisonCap](https://arxiv.org/pdf/2605.13210)).

**Lesson for a software OS:** sweeping is what you are forced into when
capabilities are unenumerable. Keeping tokens **enumerable** (kernel table /
session arena) is a design choice that buys you out of the entire sweep cost
class. Conversely, quarantine-before-reuse is worth stealing: never reuse an
object slot until its generation bump has globally propagated.

### A.6 Comparison

| Mechanism | Revoke granularity | Revoke latency | Use-time cost | Kernel entry | Persistence story |
|---|---|---|---|---|---|
| Generation bump (SimpleOS, EROS disk keys) | All caps to the record (coarse) | **O(1)** | +1 load/compare | bump = 1 write; check inline | trivial (counter is object state) |
| Caretaker / redirector (Redell, KeyKOS, CAP-III) | **Per-recipient / per-contract** | O(1) (kill proxy) | +1 indirection (worst: +1 IPC hop) | none if in-process; 1 hop if OS object | proxy is an object; persists like any object |
| seL4 CDT revoke | Subtree of derivations | **O(#descendants)**, preemptible | none | always (delegate + revoke are syscalls) | none (non-persistent kernel) |
| EROS keyrings + depend tables | Per-object, eager on prepared set | O(#prepared caps + PTEs) | prepare/deprepare bookkeeping | in-kernel | **native** (single-level store checkpoints) |
| CHERI sweep (CHERIvoke/Cornucopia) | Per-quarantined-region | epoch-length sweep (ms–s, concurrent) | ~0 (or load barrier) | kernel sweep service | none; caps in memory would persist and must be re-swept |

---

## B. ATTENUATION — the dimmer switch

Attenuation = producing a strictly weaker capability before passing it on.
The design goal is to make it a **user-space, no-kernel-round-trip operation**,
because delegation happens orders of magnitude more often than revocation.

### B.1 Monotonic narrowing (CHERI: hardware; the model to copy in a compiler)

CHERI's **guarded manipulation** rules are the cleanest statement of the
invariant: *tags can be cleared but never set; bounds can be narrowed but
never widened; permissions can be cleared but never set.* `CSetBounds`
(shrink the addressable range) and `CAndPerm` (AND-mask the permission bits)
are ordinary unprivileged instructions — attenuation costs one instruction and
**no kernel trap**; any attempt at rights amplification faults
([CHERI ISA spec, UCAM-CL-TR-907](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-907.pdf),
[CHERI hybrid architecture paper](https://cseweb.ucsd.edu/~dstefan/cse227-spring20/papers/watson:cheri.pdf)).
Monotonicity is what makes user-space attenuation *safe*: no matter how tokens
are combined, authority can only shrink along a delegation chain.

### B.2 Rights-masking on delegation (seL4, Fuchsia)

- **seL4 `Mint`**: a new cap is created from an old one with a **subset of its
  rights** plus a **badge** (an unforgeable word stamped into the cap; every
  message through a badged endpoint delivers the badge to the receiver, letting
  one server demultiplex/attenuate per client)
  ([seL4 manual cspace](https://github.com/seL4/seL4/blob/master/manual/parts/cspace.tex),
  [seL4 IPC tutorial](https://docs.sel4.systems/Tutorials/ipc.html)). Cost: a
  syscall per derivation — attenuation is kernel-mediated.
- **Fuchsia/Zircon**: every handle carries a **rights bitmap**
  (`ZX_RIGHT_DUPLICATE`, `TRANSFER`, `READ`, `WRITE`, …); `zx_handle_duplicate()`
  / `zx_handle_replace()` create a handle with **reduced** rights; two handles
  to one object can carry different rights
  ([Zircon rights](https://fuchsia.dev/fuchsia-src/concepts/kernel/rights),
  [Zircon handles](https://fuchsia.dev/fuchsia-src/concepts/kernel/handles)).
  Also kernel-mediated (syscall), but O(1) and allocation-light. **Job
  policies** add a second monotone axis: a nested job's policy can only be
  made *more* restrictive than its parent's
  ([Zircon concepts](https://fuchsia.dev/fuchsia-src/concepts/kernel/concepts)).

### B.3 OCap-language attenuation: forwarders, caretakers, membranes

The E-language tradition treats attenuation as *ordinary programming*
([Capability Myths Demolished](https://papers.agoric.com/assets/pdf/papers/capability-myths-demolished.pdf)):

- **Attenuating forwarder:** an object that holds the real reference and
  exposes only a narrower protocol (read-only view; only `today()`'s events;
  rate-limited). Zero kernel involvement; cost = one virtual dispatch.
- **Revocable forwarder / caretaker:** forwarder + a gate flag; the maker
  keeps the gate, the grantee gets the forwarder. This *combines* attenuation
  with selective revocation.
- **The leak:** a plain forwarder passes through arguments and *results*
  unwrapped — any capability returned by the wrapped object escapes the
  boundary un-attenuated
  ([Walnut, Capability Patterns](http://wiki.erights.org/wiki/Walnut/Secure_Distributed_Computing/Capability_Patterns)).
- **The membrane** fixes it **transitively**: every reference crossing the
  boundary — in arguments, return values, thrown errors — is itself wrapped in
  the same policy. A correct membrane keeps **two maps** (object→wrapper, so
  each object has one canonical wrapper and identity is preserved inside the
  membrane; wrapper→object, so references passed *back in* are unwrapped
  rather than double-wrapped)
  ([Walnut patterns](http://wiki.erights.org/wiki/Walnut/Secure_Distributed_Computing/Capability_Patterns),
  [Murϕ analysis of OCap patterns](https://cseweb.ucsd.edu/~dstefan/pubs/stefan:2011:ocap.pdf),
  [Van Cutsem & Miller, Proxies](https://dl.acm.org/doi/pdf/10.1145/1869631.1869638)).
  Revoking the membrane's single gate severs the **entire object graph** at
  once — "dry revocation."
- **KeyKOS sense keys** are the kernel-level ancestor: a sense key is the
  "weakest sensory version" of a key; fetching *any* key through a sense key
  yields the sensory (read-only) version of that key too — **transitive
  read-only attenuation enforced by the kernel** on a whole data structure,
  with no wrappers at all
  ([KeyKOS sensory keys](http://www.cap-lore.com/CapTheory/KK/Arch/Sensory.Keys.html),
  [Security in KeyKOS](http://www.cap-lore.com/Agorics/Library/KeyKos/securityInKeyKOS.html)).
- **Pony** shows the compile-time end of the spectrum: *deny* capabilities
  (`iso`, `val`, `ref`, `box`, `tag`) state what aliases may **not** do, and the
  compiler proves it — attenuation with **zero runtime cost**
  ([Deny Capabilities for Safe, Fast Actors](https://www.ponylang.io/media/papers/fast-cheap.pdf),
  [Pony object capabilities](https://tutorial.ponylang.io/object-capabilities/object-capabilities.html)).

### B.4 The LLM use case: read-only, time-boxed calendar

Hand an LLM task a membrane-wrapped calendar:
`membrane(calendar, policy = {rights: READ, deadline: t+15min, session: S})`.
Every object reachable from the calendar (events, attendee lists, attachment
handles) crosses the membrane and inherits {read-only, deadline, session S}.
Revocation is threefold and layered: the policy self-expires at the deadline
(time-box), the orchestrator can kill the membrane gate early (selective), and
session-S teardown bumps the session epoch (bulk, §C). KeyKOS sense-key
semantics ("no non-sensory key can be obtained through a sense key") is the
invariant the membrane must enforce; Pony/CHERI-style monotonicity is what
makes it checkable in the compiler rather than trusted in the library.

---

## C. SESSION SEPARATION

How does a login / an LLM task instance get an isolated capability context
with clean teardown?

- **seL4: CSpace as the context.** Each thread's TCB points at its CSpace
  (root CNode); all syscalls name capabilities *relative to that CSpace*
  ([seL4 capabilities tutorial](https://docs.sel4.systems/Tutorials/capabilities.html)).
  A "session" = a freshly built CSpace populated with exactly the session's
  caps; teardown = revoke+delete the root CNode (deleting the last cap to a
  CNode deletes the caps it contains — cascading teardown), plus CDT-revoke of
  anything minted out of the session's untyped memory. Cost: O(session caps).
- **Fuchsia: the job tree.** All processes live in a single rooted tree of
  **jobs**; a session is a job; `zx_task_kill(job)` terminates every process
  and thread beneath it, and handle cleanup destroys kernel objects whose last
  handle dies with the session. Job policies are restrict-only down the tree —
  a session can never widen its authority
  ([Zircon concepts](https://fuchsia.dev/fuchsia-src/concepts/kernel/concepts),
  [Zircon handles](https://fuchsia.dev/fuchsia-src/concepts/kernel/handles)).
- **Genode: sessions as the first-class unit.** Every service relationship is
  a **session**, created via the parent, labeled with the client identity, and
  funded by a **client-provided RAM + capability quota**. The session
  interface is an RPC object; when the RPC object is destructed, *the kernel
  invalidates its capability, implicitly revoking every delegated copy* —
  and a parent can enforce teardown by destroying an uncooperative server
  ([Genode: capability-based security](https://genode.org/documentation/genode-foundations/20.05/architecture/Capability-based_security.html),
  [Genode: common session interfaces](https://genode.org/documentation/genode-foundations/19.05/components/Common_session_interfaces.html),
  [Genode: inter-component communication](https://genode.org/documentation/genode-foundations/21.05/architecture/Inter-component_communication.html)).
  Genode is the closest existing model to "capability-scoped-to-session":
  quota makes sessions accountable, labels make them auditable, and
  object-death makes revocation implicit.

**Synthesis.** A session context needs: (1) an **enumerable container** of
every cap granted during the session (arena/CSpace/job), (2) an **epoch**
so teardown is O(1) even before the container is swept, and (3) a **quota** so
a session cannot exhaust the global cap table. Teardown then = bump epoch
(instant logical revoke) + background-free the arena (bounded sweep, EROS-style
eager cleanup of hot state).

---

## D. RECOMMENDED DESIGN for SimpleOS

Combine four layers, each covering the previous layer's blind spot. SimpleOS
already has L4-style IPC, generation tokens, and — decisively — **its own
compiler**, which lets it get CHERI/Pony-grade user-space attenuation without
hardware.

### D.1 Layer 1 — per-object generation counters (bulk revoke, O(1))

Keep the existing token shape but move from one global `next_generation` to a
**per-slot generation in a kernel cap table**, so validity checking is an
indexed compare, not a per-task list scan, and bulk revoke is per-object.

### D.2 Layer 2 — kernel Gate objects (caretaker, selective revoke, O(1))

A `Gate` is a tiny kernel redirector slot (Redell/KeyKOS, but in-kernel so the
"extra hop" is one table indirection on the syscall path, **not** an extra IPC
message). Grants to distinct recipients mint distinct gates. Revoke one
recipient = kill one gate. Gates chain (re-delegation makes a child gate
pointing at the parent gate) with a small depth bound; the kernel may flatten
chains at mint time by intersecting masks.

### D.3 Layer 3 — compiler-enforced monotonic attenuation (user space, free)

Expose capabilities in Simple as a linear/affine `Cap<T, R>` type where `R` is
a rights row/const-generic. `attenuate` is a **pure user-space function**
`Cap<T, R> -> Cap<T, R2> where R2 ⊆ R` — the subset constraint is checked at
compile time (Pony-style deny reasoning; CHERI-style monotonicity), so no
kernel call happens until the cap is actually *used* (the kernel re-checks the
rights mask on use — defense in depth against a compromised compiler/toolchain).
The stdlib membrane (`std.cap.membrane`) implements transitive attenuation
with the two-map construction (§B.3) for object graphs handed to LLM tasks,
with sense-key semantics: any cap fetched *through* the membrane is itself
membrane-wrapped, and the whole graph dies with the membrane's gate.

### D.4 Layer 4 — session arenas (O(1) teardown)

Every cap slot records its owning **session**. A session owns a contiguous
**arena** of cap-table slots and an **epoch**. Session end = bump epoch
(instant logical revocation of every cap the session ever held or minted) +
lazy arena reclaim. Cross-session delegation is only possible through an
explicit escrow gate owned by the *receiving* session — so teardown can never
leak authority out of a dead session (Genode quota + Zircon job-kill
semantics).

### D.5 Data structures

```text
# ---- kernel cap table (the only place authority lives) ----
struct CapToken:                 # user-visible; unforgeable only w.r.t. table
    slot:      u32               # index into kernel cap table
    slot_gen:  u32               # must match CapSlot.slot_gen

struct CapSlot:                  # 32 B; kernel cap table entry
    kind:       u8               # OBJECT | GATE | FREE
    session:    u16              # owning session id
    slot_gen:   u32              # bumped on free/reuse (quarantine: reuse only
                                 #   after gen bump is visible on all cores)
    rights:     u32              # bitmask; monotone: children AND-mask only
    badge:      u64              # seL4-style demux word, set at mint
    target:     u32              # OBJECT: object id | GATE: parent slot index
    object_gen: u64              # snapshot of ObjectHeader.current_gen at mint

struct ObjectHeader:             # embedded in every kernel object
    current_gen: u64             # bump => bulk-revoke all caps to this object

struct Gate:                     # stored in a CapSlot with kind = GATE
    alive:       bool            # cleared => selective revoke, O(1)
    rights_mask: u32             # intersected on every traversal
    deadline:    u64?            # optional time-box (auto-revoke)

struct Session:
    id:        u16
    epoch:     u32               # bump => all session caps logically dead
    arena:     SlotRange         # contiguous slots; lazy reclaim after bump
    cap_quota: u32               # Genode-style accountable budget
    parent:    u16               # Zircon-style tree; kill cascades to children

# ---- check-on-use (every IPC / syscall referencing a cap) ----
fn cap_check(tok, need_rights) -> u32?:      # returns object id or nil
    s = table[tok.slot]
    if s.slot_gen != tok.slot_gen: return nil          # slot reused/freed
    if sessions[s.session].epoch != epoch_at(tok):     # session dead
        return nil                                     #   (epoch cached in slot)
    r = s.rights
    while s.kind == GATE:                              # bounded depth (<= 4)
        g = gate_of(s)
        if !g.alive or now() > g.deadline: return nil  # selective / time-box
        r &= g.rights_mask
        s = table[s.target]
    if objects[s.target].current_gen != s.object_gen: return nil   # bulk revoke
    if need_rights & ~r: return nil                    # attenuation honored
    s.target
```

**Cost sheet.** Use: 3–4 indexed loads + compares (gate depth 0–1 typical).
Bulk revoke (all caps to object): 1 write. Selective revoke (one grantee):
1 write. Session teardown: 1 write + lazy sweep of one arena. Audit
("who holds X?"): scan cap table — acceptable because the table is enumerable
(the property CHERI lacks and pays sweeps for). What is deliberately dropped:
a full seL4 CDT — the gate chain *is* the derivation record for the cases that
matter, and generation bumps subsume recursive revoke at O(1) instead of
O(descendants); the trade is that "revoke exactly this subtree but not that
one" beyond gate granularity is unsupported, and each delegation costs one
table slot from the session's quota.

**Migration from `capability.spl`:** (1) replace global `next_generation`
with `ObjectHeader.current_gen` + `CapSlot.slot_gen`; (2) turn per-task
`CapabilitySet` arrays into arena ranges of the kernel table; (3) `grant()`
becomes `mint_gate()`; (4) `pledge()` becomes a self-applied AND-mask (already
monotone); (5) add the `Cap<T, R>` compile-time surface in stdlib and route
`unveil`-style path caps through it.

---

## Sources (indexed via web search; fetched summaries cited inline)

- seL4: [manual](https://sel4.systems/Info/Docs/seL4-manual-latest.pdf) · [capabilities tutorial](https://docs.sel4.systems/Tutorials/capabilities.html) · [IPC tutorial](https://docs.sel4.systems/Tutorials/ipc.html) · [cspace.tex](https://github.com/seL4/seL4/blob/master/manual/parts/cspace.tex) · [CNode.lhs (cteRevoke)](https://github.com/NICTA/seL4/blob/master/haskell/src/SEL4/Object/CNode.lhs) · [refinement paper (MDB/CTE)](https://trustworthy.systems/publications/nicta_full_text/3087.pdf)
- Revocation survey: [A Simple and Efficient Object-Capability Revocation Method (ITCC 2022)](https://dl.acm.org/doi/fullHtml/10.1145/3548636.3548656)
- KeyKOS: [nanokernel architecture](https://css.csail.mit.edu/6.5660/2017/readings/keykos.pdf) · [sensory keys](http://www.cap-lore.com/CapTheory/KK/Arch/Sensory.Keys.html) · [security in KeyKOS](http://www.cap-lore.com/Agorics/Library/KeyKos/securityInKeyKOS.html) · [capability indirection](http://www.cap-lore.com/CapTheory/Segregate.html)
- EROS: [SOSP'99 paper](https://flint.cs.yale.edu/cs428/doc/eros.pdf) · [IEEE overview](https://flint.cs.yale.edu/cs428/doc/eros-ieee.pdf)
- CHERI: [CHERIvoke (MICRO'19)](https://www.cl.cam.ac.uk/research/security/ctsrd/pdfs/201910micro-cheri-temporal-safety.pdf) · [Cornucopia (S&P'20)](https://www.cl.cam.ac.uk/research/security/ctsrd/pdfs/2020oakland-cornucopia.pdf) · [Cornucopia Reloaded (ASPLOS'24)](https://www.cl.cam.ac.uk/research/security/ctsrd/pdfs/202404asplos-cornucopia-reloaded.pdf) · [ISA spec TR-907](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-907.pdf) · [hybrid architecture](https://cseweb.ucsd.edu/~dstefan/cse227-spring20/papers/watson:cheri.pdf) · [PICASSO](https://arxiv.org/pdf/2602.09131) · [PoisonCap](https://arxiv.org/pdf/2605.13210)
- OCap patterns: [Capability Myths Demolished](https://papers.agoric.com/assets/pdf/papers/capability-myths-demolished.pdf) · [Walnut capability patterns (caretaker/membrane)](http://wiki.erights.org/wiki/Walnut/Secure_Distributed_Computing/Capability_Patterns) · [Murϕ analysis](https://cseweb.ucsd.edu/~dstefan/pubs/stefan:2011:ocap.pdf) · [Proxies (Van Cutsem & Miller)](https://dl.acm.org/doi/pdf/10.1145/1869631.1869638)
- Pony: [Deny Capabilities paper](https://www.ponylang.io/media/papers/fast-cheap.pdf) · [tutorial](https://tutorial.ponylang.io/object-capabilities/object-capabilities.html)
- Fuchsia/Zircon: [rights](https://fuchsia.dev/fuchsia-src/concepts/kernel/rights) · [handles](https://fuchsia.dev/fuchsia-src/concepts/kernel/handles) · [kernel concepts (jobs)](https://fuchsia.dev/fuchsia-src/concepts/kernel/concepts)
- Genode: [capability-based security](https://genode.org/documentation/genode-foundations/20.05/architecture/Capability-based_security.html) · [session interfaces](https://genode.org/documentation/genode-foundations/19.05/components/Common_session_interfaces.html) · [inter-component communication](https://genode.org/documentation/genode-foundations/21.05/architecture/Inter-component_communication.html)
