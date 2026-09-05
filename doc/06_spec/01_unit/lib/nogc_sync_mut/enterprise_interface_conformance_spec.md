# Interface Conformance — the frozen contract surface, mechanically asserted

> `enterprise_conformance_spec.spl` proves the guarded-command SEQUENCE (replay, one-effect, tenant scoping) by driving full business flows. This spec is its narrower sibling: it fences the two INTERFACE invariants of the frozen contract layer (`enterprise_sale/foundation.spl` + the `enterprise_store` durable API), independent of any single vertical's business logic, so a drift in the contract surface is caught even if every vertical's flow still passes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interface Conformance — the frozen contract surface, mechanically asserted

`enterprise_conformance_spec.spl` proves the guarded-command SEQUENCE (replay, one-effect, tenant scoping) by driving full business flows. This spec is its narrower sibling: it fences the two INTERFACE invariants of the frozen contract layer (`enterprise_sale/foundation.spl` + the `enterprise_store` durable API), independent of any single vertical's business logic, so a drift in the contract surface is caught even if every vertical's flow still passes.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/simple_enterprise_suite/state.md |
| Design | doc/07_guide/app/enterprise/README.md |
| Source | `test/01_unit/lib/nogc_sync_mut/enterprise_interface_conformance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`enterprise_conformance_spec.spl` proves the guarded-command SEQUENCE (replay,
one-effect, tenant scoping) by driving full business flows. This spec is its
narrower sibling: it fences the two INTERFACE invariants of the frozen contract
layer (`enterprise_sale/foundation.spl` + the `enterprise_store` durable API),
independent of any single vertical's business logic, so a drift in the contract
surface is caught even if every vertical's flow still passes.

Two invariants, both executable — never grep, never prose:

1. **Closed reason set.** `reason_set()` is the single source of truth for
   machine-readable `CommandResult.reason` values, and `reason_allowed` is its
   executable membership oracle. Every vertical denies ONLY with a member.
   Proven three ways: (a) the frozen list has exactly 16 entries and each is
   `reason_allowed`; (b) a live denial driven out of EVERY vertical is a member;
   (c) **reproduce-first bite** — a value that is deliberately NOT in the set is
   rejected. If a lane widened the set to admit a bogus reason, assertion (c)
   goes red immediately.

2. **Cross-OS hashing facade.** Audit and credential hashing route through
   `enterprise_store/audit_hash.audit_sha256_hex`, NOT `std.common.crypto.sha256`
   directly. The facade exists because `sha256_text` drags slice / `[v; n]`
   CollectionOps into the compile closure that standalone-SMF (SimpleOS) codegen
   rejects (see `audit_hash.spl` header). The facade's contract is that it is
   DIGEST-IDENTICAL to the std hash, so a vertical that routes through it gets a
   byte-identical audit chain on every OS. This spec pins that identity to the
   canonical SHA-256 test vectors AND to `sha256_text` itself, so a divergence
   in the facade (which would silently corrupt the cross-OS audit chain) goes
   red. The audit chain, built through the facade, is then verified end to end.

## Known coherence finding (recorded, not fixed here — W19-C audit)

`enterprise_payment/payment.spl:59,78` imports and calls `sha256_text` DIRECTLY
for `provider_sign` / `provider_verify`, bypassing the facade. That is a
cross-OS invariant violation owned by the payment lane, not the contract layer:
it does not affect the audit chain (payment's own audit rows still route through
the store's facade), but it means the payment vertical will not build under
standalone-SMF. Recorded in the guide's coherence matrix
(`doc/07_guide/app/enterprise/README.md`) and the feature-expert wiki. This spec
guards the FACADE's correctness so that the fix (swap the import to
`audit_sha256_hex`) is provably digest-preserving.

**Requirements:** N/A
**Plan:** .spipe/simple_enterprise_suite/state.md
**Design:** doc/07_guide/app/enterprise/README.md

Lane: .spipe/simple_enterprise_suite (W19-C).

## Scenarios

### interface conformance — closed reason set

#### the frozen set has exactly 16 members and each is reason_allowed

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- the frozen set has exactly 16 members and each is reason_allowed
- reason_set is the frozen source of truth
   - Expected: reason_set().len() equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("the frozen set has exactly 16 members and each is reason_allowed")
step("reason_set is the frozen source of truth")
expect(reason_set().len()).to_equal(16)
for r in reason_set():
    expect(reason_allowed(r)).to_be(true)
```

</details>

#### reproduce-first bite: a value outside the set is rejected

- reproduce-first bite: a value outside the set is rejected
- Values that are NOT machine-readable members must fail the oracle


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reproduce-first bite: a value outside the set is rejected")
step("Values that are NOT machine-readable members must fail the oracle")
# If a lane widened reason_set() to admit any of these, this scenario
# goes red — that is the whole point of a CLOSED set.
expect(reason_allowed("__spec_bogus_reason__")).to_be(false)
expect(reason_allowed("")).to_be(false)
expect(reason_allowed("Accepted")).to_be(false)       # case matters
expect(reason_allowed("duplicate_key")).to_be(false)  # underscore, not hyphen
expect(reason_allowed("ok")).to_be(false)
```

</details>

#### a live denial driven out of EVERY vertical is a member of the closed set

- a live denial driven out of EVERY vertical is a member of the closed set
- Seed one store shared across every vertical's migrations
- Guarded verticals: an inactive session denies at the first rung
- Session vertical: a wrong-secret issuance is the generic, non-enumerating denial
- Every collected reason is inside the closed set; the set is non-trivial
   - Expected: reasons.len() equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a live denial driven out of EVERY vertical is a member of the closed set")
step("Seed one store shared across every vertical's migrations")
val store = fresh_store("reasons")
val t = tenant_a()
val admin = admin_a()
val dead = dead_session()
sale_setup(store)
booking_setup(store)
restaurant_setup(store)
payment_setup(store)
hcm_setup(store)
proc_setup(store)
fin_setup(store)
channel_setup(store)
session_setup(store)

step("Guarded verticals: an inactive session denies at the first rung")
var reasons: [text] = []
reasons.push(sale_place_order(store, dead, t, admin, envelope("if-1"), "o-1", "SKU-1", 1).reason)
reasons.push(booking_hold(store, dead, t, admin, envelope("if-2"), "b-1", "res-1", 1, 2, 1, "", 0, 10).reason)
reasons.push(order_add_line(store, dead, t, admin, envelope("if-3"), "sess-1", "l-1", "SKU-1", 1, "").reason)
reasons.push(payment_create_intent(store, dead, t, admin, envelope("if-4"), "int-1", "o-1", 1).reason)
reasons.push(hcm_clock_in(store, dead, t, admin, envelope("if-5"), "emp-1", 1).reason)
reasons.push(proc_requisition_create(store, dead, t, admin, envelope("if-6"), "req-1", "SKU-1", 1).reason)
reasons.push(fin_period_close(store, dead, t, admin, envelope("if-7"), 100, 200).reason)
reasons.push(channel_register(store, dead, t, admin, "ch-1", "mock").reason)

step("Session vertical: a wrong-secret issuance is the generic, non-enumerating denial")
# credential_seed is itself a guarded write and needs an ACTIVE admin
# session; only the subsequent session_issue is the unauthenticated path.
credential_seed(store, admin_session(), t, admin, "user-1", "sales", "salt", "secret")
reasons.push(session_issue(store, "tenant-a", "user-1", "wrong", 100, 900, "entropy-conformance-x").reason)

step("Every collected reason is inside the closed set; the set is non-trivial")
expect(reasons.len()).to_equal(9)
for r in reasons:
    expect(reason_allowed(r)).to_be(true)
store_close(store)
```

</details>

### interface conformance — cross-OS hashing facade

#### audit_sha256_hex matches the canonical SHA-256 test vectors

- audit_sha256_hex matches the canonical SHA-256 test vectors
- Known-answer vectors pin the facade (bite: any drift goes red here)
   - Expected: audit_sha256_hex("") equals `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`
   - Expected: audit_sha256_hex("abc") equals `ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("audit_sha256_hex matches the canonical SHA-256 test vectors")
step("Known-answer vectors pin the facade (bite: any drift goes red here)")
expect(audit_sha256_hex("")).to_equal("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
expect(audit_sha256_hex("abc")).to_equal("ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
```

</details>

#### the facade is digest-identical to std.common.crypto.sha256.sha256_text

- the facade is digest-identical to std.common.crypto.sha256.sha256_text
- The facade contract: same digest as the std hash, on every OS
   - Expected: audit_sha256_hex(s) equals `sha256_text(s)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("the facade is digest-identical to std.common.crypto.sha256.sha256_text")
step("The facade contract: same digest as the std hash, on every OS")
val samples = ["", "abc", "tenant-a|admin-1|sale.order.place|o-1", "the quick brown fox"]
for s in samples:
    expect(audit_sha256_hex(s)).to_equal(sha256_text(s))
```

</details>

#### the store's audit chain, built through the facade, verifies end to end

- the store's audit chain, built through the facade, verifies end to end
- A guarded write records an audit row hashed via the facade
   - Expected: credential_seed(store, admin_session(), t, admin, "user-1", "sales", "salt", "secret").reason equals `accepted`
- The facade-hashed chain is internally consistent


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("the store's audit chain, built through the facade, verifies end to end")
step("A guarded write records an audit row hashed via the facade")
val store = fresh_store("facade")
val t = tenant_a()
val admin = admin_a()
session_setup(store)
# credential_seed is an accepted guarded write: it appends a
# facade-hashed audit row for tenant-a.
expect(credential_seed(store, admin_session(), t, admin, "user-1", "sales", "salt", "secret").reason).to_equal("accepted")
step("The facade-hashed chain is internally consistent")
expect(audit_verify_chain(store, "tenant-a")).to_be(true)
store_close(store)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `.spipe/simple_enterprise_suite/state.md`
- **Design:** `doc/07_guide/app/enterprise/README.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6b6d8d94a30094a14711cc6c479b99afccde0acd0e8d00193fac7efe171d3afc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6b6d8d94a30094a14711cc6c479b99afccde0acd0e8d00193fac7efe171d3afc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6b6d8d94a30094a14711cc6c479b99afccde0acd0e8d00193fac7efe171d3afc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/nogc_sync_mut/enterprise_interface_conformance_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_interface_conformance_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_interface_conformance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_interface_conformance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/enterprise_interface_conformance_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/enterprise_interface_conformance_spec.spl:125:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the frozen set has exactly 16 members and each is reason_allowed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_interface_conformance_spec.spl:133:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reproduce-first bite: a value outside the set is rejected' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_interface_conformance_spec.spl:145:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a live denial driven out of EVERY vertical is a member of the closed set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
