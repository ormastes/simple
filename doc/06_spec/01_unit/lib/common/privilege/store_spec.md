# PrivilegeStore Specification

> Covers lookup/mint/revoke round-trip, group expansion, and SDN save/load

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# PrivilegeStore Specification

Covers lookup/mint/revoke round-trip, group expansion, and SDN save/load

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Red (no impl yet) |
| Source | `test/01_unit/lib/common/privilege/store_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Covers lookup/mint/revoke round-trip, group expansion, and SDN save/load
round-trip via `store_fs` (see Phase 3 interfaces).

## Scenarios

### PrivilegeStore

### lookup / mint / revoke

#### AC-1: mint returns a token that lookup then finds

- AC-1: mint returns a token that lookup then finds


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: mint returns a token that lookup then finds")
val store = PrivilegeStore.new()
val principal = Principal(kind: PrincipalKind.Local, id: "alice")
val parent = AuthorityToken.root_for(principal)
val child_path = id_path_intern("id.user.banking.view")
val minted = store.mint(parent, child_path, AuthorityLevel.Sensitive)
expect minted.ok to_equal true
val found = store.lookup(principal, child_path)
expect found.present to_equal true
```

</details>

#### AC-1: revoke removes the token from subsequent lookup

- AC-1: revoke removes the token from subsequent lookup


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: revoke removes the token from subsequent lookup")
val store = PrivilegeStore.new()
val principal = Principal(kind: PrincipalKind.Local, id: "alice")
val parent = AuthorityToken.root_for(principal)
val path = id_path_intern("id.user.banking.view")
val minted = store.mint(parent, path, AuthorityLevel.Sensitive)
store.revoke(minted.value.issuer_sig)
val found = store.lookup(principal, path)
expect found.present to_equal false
```

</details>

### expand_groups

#### AC-1: id.group.dev expands to member id_paths

- AC-1: id.group.dev expands to member id_paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: id.group.dev expands to member id_paths")
val store = PrivilegeStore.new()
val claude = id_path_intern("id.user.claude")
val codex = id_path_intern("id.user.codex")
val dev = id_path_intern("id.group.dev")
store.add_group(GroupDecl(id_path: dev, members: [claude, codex]))
val expanded = store.expand_groups(dev)
expect expanded to_contain claude
expect expanded to_contain codex
```

</details>

### SDN round-trip

#### AC-1: encode then decode yields equal store

- AC-1: encode then decode yields equal store


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: encode then decode yields equal store")
val store = PrivilegeStore.new()
val principal = Principal(kind: PrincipalKind.Local, id: "alice")
val parent = AuthorityToken.root_for(principal)
store.mint(parent, id_path_intern("id.user.banking.view"), AuthorityLevel.Sensitive)
val text = privilege_store_encode(store)
val decoded = privilege_store_decode(text)
expect decoded.ok to_equal true
expect decoded.value.tokens.len() to_equal store.tokens.len()
```

</details>

#### AC-1: store_fs.save_sdn / load_sdn round-trip via filesystem

- AC-1: store_fs.save_sdn / load_sdn round-trip via filesystem


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: store_fs.save_sdn / load_sdn round-trip via filesystem")
val store = PrivilegeStore.new()
val principal = Principal(kind: PrincipalKind.Local, id: "alice")
val parent = AuthorityToken.root_for(principal)
store.mint(parent, id_path_intern("id.user.mail.read"), AuthorityLevel.Internal)
val tmp = "/tmp/spm_winfs_privstore_spec.sdn"
val save_result = save_sdn(store, tmp)
expect save_result.ok to_equal true
val loaded = load_sdn(tmp)
expect loaded.ok to_equal true
expect loaded.value.tokens.len() to_equal 1
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `89f71b122fac8e26a2868410a57fdc99fce742b26e20121112edac1a41db6a92`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `89f71b122fac8e26a2868410a57fdc99fce742b26e20121112edac1a41db6a92`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `89f71b122fac8e26a2868410a57fdc99fce742b26e20121112edac1a41db6a92`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/privilege/store_spec.spl
mirror: doc/06_spec/01_unit/lib/common/privilege/store_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/privilege/store_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/privilege/store_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/privilege/store_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: mint returns a token that lookup then finds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/privilege/store_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: revoke removes the token from subsequent lookup' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/privilege/store_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: id.group.dev expands to member id_paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
