# ABI v1 Capability-Transfer Contract (Kernel IPC — lane P1)

> This is the CONTRACT spec for the two ABI v1 invariants that every capability transfer across the kernel IPC boundary must uphold. It is deliberately written against the shipping code (`os.kernel.ipc.cspace_spawn`, `os.kernel.ipc.capability`) rather than a model, so a regression in either file turns this spec red.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ABI v1 Capability-Transfer Contract (Kernel IPC — lane P1)

This is the CONTRACT spec for the two ABI v1 invariants that every capability transfer across the kernel IPC boundary must uphold. It is deliberately written against the shipping code (`os.kernel.ipc.cspace_spawn`, `os.kernel.ipc.capability`) rather than a model, so a regression in either file turns this spec red.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-HARDEN-P1-IPC |
| Category | Kernel / IPC / Security |
| Difficulty | 4/5 |
| Status | Implemented |
| Plan | doc/03_plan/agent_tasks/simpleos_production_harden_parallel.md (lane P1) |
| Research | doc/01_research/domain/simpleos_production_host_master_plan.md (§5.1, §21) |
| Source | `test/01_unit/os/kernel/ipc/abi_v1_transfer_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This is the CONTRACT spec for the two ABI v1 invariants that every capability
transfer across the kernel IPC boundary must uphold. It is deliberately written
against the shipping code (`os.kernel.ipc.cspace_spawn`, `os.kernel.ipc.capability`)
rather than a model, so a regression in either file turns this spec red.

**Invariant A — rights only attenuate (master plan §21).**
A transfer may narrow authority and may never widen it. Concretely, for every
capability the receiver ends up holding, the receiver's rights bits are a SUBSET
of the rights bits of the sender token that authorized the transfer. Asking for
rights the sender does not hold does not "clamp to what is available" — the whole
grant is REJECTED (fail closed), so a caller policy bug is loud, not silent.
Delegation depth is the second attenuating axis: a child is always minted at
`depth - 1`, and a spent (depth 0) token can never be delegated again.

**Invariant B — a one-shot authority cannot be used twice.**
SimpleOS has two one-shot mechanisms, and both are asserted here:
  - `SingleUseLedger` (this lane): a `single_use` grant arms the minted token id;
    the first `consume()` succeeds and every later one is DENIED. Before this
    lane the `single_use` flag on `AttenuationSpec` was documentation only, so a
    "one-shot" capability could be replayed forever — the guard is new, the flag
    is not.
  - `EscrowCap` / `consume_escrow` (pre-existing, in `capability.spl`): a cap
    escrowed into a receiver session is redeemable exactly once, by the intended
    receiver, while that receiver's session epoch is still live.

## Scope note (honesty)

These are the transfer-ALGEBRA contracts. They do NOT prove that two isolated
processes exchanged a handle under QEMU — that is the lane's separate runtime
gate and is not claimed by this file. `l4_fast_ipc.spl` is a benchmark model and
is not exercised here; it is not on the syscall path.

## Scenarios

### ABI v1 transfer: rights only attenuate, never widen

#### narrows the receiver to a strict subset when the recipe masks rights down

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### rejects the transfer outright when the recipe asks for rights the sender lacks

- Sender holds read only
- Recipe asks for read+write with no narrowing — a widening request
- Fail closed: the grant is DROPPED and counted, not silently clamped
   - Expected: mint.rejected equals `1`
   - Expected: mint.caps.caps.len() equals `0`
- The empty pouch is pledged, so it denies every check (not ambient-allow)


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Sender holds read only")
val sender = sender_pouch(CAP_RIGHT_READ)
step("Recipe asks for read+write with no narrowing — a widening request")
val mint = spawn_with_cspace(sender, one_grant_spec(CAP_RIGHT_READ + CAP_RIGHT_WRITE, atten_identity()), 7u64, 10u64, 800u64)
step("Fail closed: the grant is DROPPED and counted, not silently clamped")
expect(mint.rejected).to_equal(1)
expect(mint.caps.caps.len()).to_equal(0)
step("The empty pouch is pledged, so it denies every check (not ambient-allow)")
assert_true(mint.caps.is_pledged)
assert_false(mint.caps.has(_dataset(CAP_RIGHT_READ)))
```

</details>

#### cannot use the rights mask as a back door to gain a bit the sender never had

- Sender holds read only; the mask names write and admin
- Masking is an AND, so the result can only ever remove bits — and the
- residual authority is still not one the sender holds, so it is rejected
   - Expected: mint.rejected equals `1`
   - Expected: mint.caps.caps.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Sender holds read only; the mask names write and admin")
val sender = sender_pouch(CAP_RIGHT_READ)
val mask = CAP_RIGHT_WRITE + CAP_RIGHT_ADMIN
val mint = spawn_with_cspace(sender, one_grant_spec(CAP_RIGHT_READ + CAP_RIGHT_WRITE, atten_rights(mask)), 7u64, 10u64, 800u64)
step("Masking is an AND, so the result can only ever remove bits — and the")
step("residual authority is still not one the sender holds, so it is rejected")
expect(mint.rejected).to_equal(1)
expect(mint.caps.caps.len()).to_equal(0)
```

</details>

#### holds the subset invariant across every capability of a multi-grant recipe

- Sender holds read+write+map
- Three grants of the same authority, narrowed three different ways
   - Expected: mint.rejected equals `0`
   - Expected: mint.caps.caps.len() equals `3`
- EVERY minted capability's rights are a subset of the sender's rights
   - Expected: violations equals `0`
- Every minted capability is linked to the sender token that authorized it
   - Expected: unlinked equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Sender holds read+write+map")
val sender_rights = _rw_map()
val sender = sender_pouch(sender_rights)
step("Three grants of the same authority, narrowed three different ways")
val spec = SpawnSpec(
    image_hash: IMAGE_HASH,
    grants: [
        CapGrant(label: "ds.ro", requested: _dataset(sender_rights), atten: atten_rights(CAP_RIGHT_READ)),
        CapGrant(label: "ds.rw", requested: _dataset(sender_rights), atten: atten_rights(CAP_RIGHT_READ + CAP_RIGHT_WRITE)),
        CapGrant(label: "ds.full", requested: _dataset(sender_rights), atten: atten_identity())
    ],
    isolation: "sandbox",
    budget: 0u64
)
val mint = spawn_with_cspace(sender, spec, 7u64, 10u64, 800u64)
expect(mint.rejected).to_equal(0)
expect(mint.caps.caps.len()).to_equal(3)
step("EVERY minted capability's rights are a subset of the sender's rights")
var violations = 0
for tok in mint.caps.caps:
    if not _is_subset(_rights_of(tok.kind), sender_rights):
        violations = violations + 1
expect(violations).to_equal(0)
step("Every minted capability is linked to the sender token that authorized it")
var unlinked = 0
for tok in mint.caps.caps:
    if tok.parent_token_id != 500u64:
        unlinked = unlinked + 1
expect(unlinked).to_equal(0)
```

</details>

#### spends a delegation-depth budget on every hop and refuses to re-delegate a spent token

- Sender token has depth 2
   - Expected: hop1.caps.caps[0].depth equals `1`
- Forking the child spends the last unit of budget
   - Expected: hop2.caps.caps.len() equals `1`
   - Expected: hop2.caps.caps[0].depth equals `0`
- A depth-0 token is not delegable: the next hop inherits NOTHING
   - Expected: hop3.caps.caps.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Sender token has depth 2")
val sender = sender_pouch(_rw_map())
val hop1 = spawn_with_cspace(sender, one_grant_spec(_rw_map(), atten_identity()), 7u64, 10u64, 800u64)
expect(hop1.caps.caps[0].depth).to_equal(1)
step("Forking the child spends the last unit of budget")
val hop2 = fork_cspace(hop1.caps, 8u64, 20u64, 900u64)
expect(hop2.caps.caps.len()).to_equal(1)
expect(hop2.caps.caps[0].depth).to_equal(0)
step("A depth-0 token is not delegable: the next hop inherits NOTHING")
val hop3 = fork_cspace(hop2.caps, 9u64, 30u64, 950u64)
expect(hop3.caps.caps.len()).to_equal(0)
assert_true(hop3.caps.is_pledged)
```

</details>

#### refuses a CapabilityManager grant once the delegation budget is exhausted

- A depth-0 token is denied delegation by the manager, not clamped


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("A depth-0 token is denied delegation by the manager, not clamped")
var mgr = CapabilityManager.new()
mgr.init_task_record(TaskId(id: 1u64), true)
mgr.init_task_record(TaskId(id: 2u64), false)
val spent = _tok(_dataset(CAP_RIGHT_READ), 1u64, 600u64, 0)
assert_false(mgr.grant(TaskId(id: 1u64), TaskId(id: 2u64), spent))
```

</details>

### ABI v1 transfer: single-use authority is consumable exactly once

#### denies the second use of a single_use capability minted into a child C-Space

- Sender delegates a ONE-SHOT dataset capability
   - Expected: mint.rejected equals `0`
   - Expected: mint.caps.caps.len() equals `1`
- The minted token id is armed as one-shot
   - Expected: ledger.armed_count() equals `1`
- The FIRST use succeeds
- The SECOND use is DENIED — this is the replay guard
- ...and so is every use after that


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Sender delegates a ONE-SHOT dataset capability")
val sender = sender_pouch(_rw_map())
var ledger = SingleUseLedger.new()
val mint = spawn_with_cspace_tracked(sender, one_grant_spec(_rw_map(), atten_single_use()), 7u64, 10u64, 800u64, ledger)
expect(mint.rejected).to_equal(0)
expect(mint.caps.caps.len()).to_equal(1)
step("The minted token id is armed as one-shot")
val tid = mint.caps.caps[0].token_id
expect(ledger.armed_count()).to_equal(1)
assert_true(ledger.is_armed(tid))
assert_false(ledger.is_consumed(tid))
step("The FIRST use succeeds")
assert_true(ledger.consume(tid))
assert_true(ledger.is_consumed(tid))
step("The SECOND use is DENIED — this is the replay guard")
assert_false(ledger.consume(tid))
step("...and so is every use after that")
assert_false(ledger.consume(tid))
```

</details>

#### arms nothing when the single_use grant is itself rejected

- Sender holds read only but the one-shot recipe asks for read+write
- No authority was delegated, so no one-shot exists to spend
   - Expected: mint.rejected equals `1`
   - Expected: ledger.armed_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Sender holds read only but the one-shot recipe asks for read+write")
val sender = sender_pouch(CAP_RIGHT_READ)
var ledger = SingleUseLedger.new()
val mint = spawn_with_cspace_tracked(sender, one_grant_spec(CAP_RIGHT_READ + CAP_RIGHT_WRITE, atten_single_use()), 7u64, 10u64, 800u64, ledger)
step("No authority was delegated, so no one-shot exists to spend")
expect(mint.rejected).to_equal(1)
expect(ledger.armed_count()).to_equal(0)
assert_false(ledger.is_armed(800u64))
```

</details>

#### refuses to re-arm a spent one-shot back into a fresh one

- Mint and spend a one-shot
- Re-arming the same token id is refused, so the spend cannot be refunded
   - Expected: ledger.armed_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Mint and spend a one-shot")
val sender = sender_pouch(_rw_map())
var ledger = SingleUseLedger.new()
val mint = spawn_with_cspace_tracked(sender, one_grant_spec(_rw_map(), atten_single_use()), 7u64, 10u64, 800u64, ledger)
val tid = mint.caps.caps[0].token_id
assert_true(ledger.consume(tid))
step("Re-arming the same token id is refused, so the spend cannot be refunded")
assert_false(ledger.arm(tid))
assert_false(ledger.consume(tid))
expect(ledger.armed_count()).to_equal(1)
```

</details>

#### denies a token that was never armed as one-shot (fail closed)

- A plain, non-single_use transfer arms nothing
   - Expected: ledger.armed_count() equals `0`
- consume() on an unarmed token id denies rather than accidentally allowing


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("A plain, non-single_use transfer arms nothing")
val sender = sender_pouch(_rw_map())
var ledger = SingleUseLedger.new()
val mint = spawn_with_cspace_tracked(sender, one_grant_spec(_rw_map(), atten_identity()), 7u64, 10u64, 800u64, ledger)
expect(ledger.armed_count()).to_equal(0)
step("consume() on an unarmed token id denies rather than accidentally allowing")
assert_false(ledger.consume(mint.caps.caps[0].token_id))
assert_false(ledger.consume(4242u64))
```

</details>

#### redeems an escrowed capability exactly once, and only by the intended receiver

- Two live sessions: a sender holding the dataset cap, and a receiver
- Sender escrows a SINGLE-USE cap into the receiver's arena
- A third party cannot redeem it
- The intended receiver redeems it once — this must succeed
- The SECOND redemption is DENIED — one-shot means one shot
- ...and the third party still cannot redeem the spent escrow


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Two live sessions: a sender holding the dataset cap, and a receiver")
var mgr = CapabilityManager.new()
val cap = _tok(_dataset(CAP_RIGHT_READ), 1u64, 700u64, 2)
val from_s = mgr.login("scheduler", CapabilitySet(caps: [cap], is_pledged: true))
val to_s = mgr.login("ticketing", CapabilitySet(caps: [], is_pledged: true))
val other = mgr.login("intruder", CapabilitySet(caps: [], is_pledged: true))
step("Sender escrows a SINGLE-USE cap into the receiver's arena")
val esc_opt = mgr.escrow_cap(from_s.id, to_s.id, cap)
assert_true(esc_opt != nil)
val esc = esc_opt
assert_false(esc.consumed)
step("A third party cannot redeem it")
assert_true(mgr.consume_escrow(esc.id, other.id) == nil)
step("The intended receiver redeems it once — this must succeed")
assert_true(mgr.consume_escrow(esc.id, to_s.id) != nil)
step("The SECOND redemption is DENIED — one-shot means one shot")
assert_true(mgr.consume_escrow(esc.id, to_s.id) == nil)
step("...and the third party still cannot redeem the spent escrow")
assert_true(mgr.consume_escrow(esc.id, other.id) == nil)
```

</details>

#### never escrows authority the sender does not currently hold

- Sender's session holds read only; it tries to escrow write
- Monotonic guard: an escrow can never exceed the sender's current authority


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Sender's session holds read only; it tries to escrow write")
var mgr = CapabilityManager.new()
val held = _tok(_dataset(CAP_RIGHT_READ), 1u64, 710u64, 2)
val wanted = _tok(_dataset(CAP_RIGHT_WRITE), 2u64, 711u64, 2)
val from_s = mgr.login("scheduler", CapabilitySet(caps: [held], is_pledged: true))
val to_s = mgr.login("ticketing", CapabilitySet(caps: [], is_pledged: true))
step("Monotonic guard: an escrow can never exceed the sender's current authority")
assert_true(mgr.escrow_cap(from_s.id, to_s.id, wanted) == nil)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/simpleos_production_harden_parallel.md (lane P1)`
- **Research:** `doc/01_research/domain/simpleos_production_host_master_plan.md (§5.1, §21)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7fab15d464465f1136e009f4e2cd0a341eba4c3702c12228a48dff085fb34fdf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7fab15d464465f1136e009f4e2cd0a341eba4c3702c12228a48dff085fb34fdf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7fab15d464465f1136e009f4e2cd0a341eba4c3702c12228a48dff085fb34fdf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/01_unit/os/kernel/ipc/abi_v1_transfer_contract_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/ipc/abi_v1_transfer_contract_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/ipc/abi_v1_transfer_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/ipc/abi_v1_transfer_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/ipc/abi_v1_transfer_contract_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/os/kernel/ipc/abi_v1_transfer_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 19 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/ipc/abi_v1_transfer_contract_spec.spl:110:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'narrows the receiver to a strict subset when the recipe masks rights down' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/kernel/ipc/abi_v1_transfer_contract_spec.spl:129:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects the transfer outright when the recipe asks for rights the sender lacks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/ipc/abi_v1_transfer_contract_spec.spl:141:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cannot use the rights mask as a back door to gain a bit the sender never had' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/ipc/abi_v1_transfer_contract_spec.spl:151:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'holds the subset invariant across every capability of a multi-grant recipe' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
