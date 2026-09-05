# RBAC Registry Equivalence — data-driven table matches the frozen if-chain

> For the FULL cross-product of every role × every action string in the suite —

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RBAC Registry Equivalence — data-driven table matches the frozen if-chain

For the FULL cross-product of every role × every action string in the suite —

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/simple_enterprise_suite/state.md |
| Design | src/lib/nogc_sync_mut/enterprise_sale/rbac_registry.spl |
| Source | `test/01_unit/lib/nogc_sync_mut/enterprise_rbac_registry_equivalence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## What is proven

For the FULL cross-product of every role × every action string in the suite —
including an unknown role, an empty role, and deny-only actions no role owns —
`registry_role_allows(role, action)` returns EXACTLY what
`foundation.role_allows(role, action)` returns. This is behavioural identity,
not a spot check: the loop compares every pair and fails on the first that
disagrees.

The action set is enumerated HERE, independently of both implementations, read
straight out of `foundation.role_allows`'s grants (transcribed once, in this
file), so the spec is a genuine external oracle and not a mirror of the
registry data it checks.

## Why it bites

Dropping or altering a single registry grant makes exactly one pair disagree
and turns this spec red on that pair. The bite proof (a temporary grant
removal → red → restore → green) is recorded in the W15-B state entry.

**Requirements:** N/A
**Plan:** .spipe/simple_enterprise_suite/state.md
**Design:** src/lib/nogc_sync_mut/enterprise_sale/rbac_registry.spl

Lane: .spipe/simple_enterprise_suite (W15-B).

## Scenarios

### rbac registry equivalence — data-driven table matches frozen role_allows

#### agrees with foundation.role_allows across the full role x action cross-product

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- agrees with foundation.role_allows across the full role x action cross-product
- Cross-product every role x every action; each pair must agree
   - Expected: data equals `frozen`
- The cross-product is the expected size and is non-trivial
   - Expected: pairs equals `290`
   - Expected: granted equals `53`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("agrees with foundation.role_allows across the full role x action cross-product")
step("Cross-product every role x every action; each pair must agree")
val roles = every_role()
val actions = every_action()
var pairs: i64 = 0
var granted: i64 = 0
for r in roles:
    for a in actions:
        val frozen = role_allows(r, a)
        val data = registry_role_allows(r, a)
        expect(data).to_equal(frozen)
        pairs = pairs + 1
        if frozen:
            granted = granted + 1

step("The cross-product is the expected size and is non-trivial")
# 10 roles x 29 actions = 290 pairs compared.
expect(pairs).to_equal(290)
# admin grants all 29; sales 3; payments 3; procurement 5; booking 4;
# finance 2; hcm 7; the three ungranted roles 0 => 29+3+3+5+4+2+7 = 53.
expect(granted).to_equal(53)
```

</details>

#### admin is allowed every action and unknown roles are allowed none

- admin is allowed every action and unknown roles are allowed none
- admin passes every action string in the suite
- an unknown role is denied every action string


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("admin is allowed every action and unknown roles are allowed none")
step("admin passes every action string in the suite")
for a in every_action():
    expect(registry_role_allows("admin", a)).to_be(true)

step("an unknown role is denied every action string")
for a in every_action():
    expect(registry_role_allows("customer", a)).to_be(false)
```

</details>

#### the registry data covers exactly the six non-admin roles

- the registry data covers exactly the six non-admin roles
- rbac_registry has one row per non-admin role, admin absent
   - Expected: rows.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("the registry data covers exactly the six non-admin roles")
step("rbac_registry has one row per non-admin role, admin absent")
val rows = rbac_registry()
expect(rows.len()).to_equal(6)
var has_admin_row: bool = false
for g in rows:
    if g.role == "admin":
        has_admin_row = true
expect(has_admin_row).to_be(false)
```

</details>

#### each granted action round-trips true through the data-driven oracle

- each granted action round-trips true through the data-driven oracle
- Every action listed in a grant row is allowed for that row's role


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("each granted action round-trips true through the data-driven oracle")
step("Every action listed in a grant row is allowed for that row's role")
for g in rbac_registry():
    for a in g.actions:
        expect(registry_role_allows(g.role, a)).to_be(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `.spipe/simple_enterprise_suite/state.md`
- **Design:** `src/lib/nogc_sync_mut/enterprise_sale/rbac_registry.spl`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8c9248fe60e5c822488384bd29f68cbefeb9bce797ad98381285ef168496c0cc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8c9248fe60e5c822488384bd29f68cbefeb9bce797ad98381285ef168496c0cc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8c9248fe60e5c822488384bd29f68cbefeb9bce797ad98381285ef168496c0cc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_sync_mut/enterprise_rbac_registry_equivalence_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_rbac_registry_equivalence_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_rbac_registry_equivalence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_rbac_registry_equivalence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/enterprise_rbac_registry_equivalence_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/enterprise_rbac_registry_equivalence_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agrees with foundation.role_allows across the full role x action cross-product' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_rbac_registry_equivalence_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admin is allowed every action and unknown roles are allowed none' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_rbac_registry_equivalence_spec.spl:120:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the registry data covers exactly the six non-admin roles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
