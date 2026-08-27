# SFM Dependency Injection & AOP Authorization

> Exposed layers are linked to an app through data-driven dependency injection (`register_layers` loops the manifest — no hard-coded wiring) and resolved by role (`resolve_layer`). Layer access is guarded by an AOP Around interceptor that enforces the module's security level: `Trusted`/privileged layers require a granted context, otherwise resolution is denied. This spec covers AC-3 (resolve-by-role, data-driven), AC-4 (AOP allow/deny), and AC-5 (the special `Trusted` security level gating).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SFM Dependency Injection & AOP Authorization

Exposed layers are linked to an app through data-driven dependency injection (`register_layers` loops the manifest — no hard-coded wiring) and resolved by role (`resolve_layer`). Layer access is guarded by an AOP Around interceptor that enforces the module's security level: `Trusted`/privileged layers require a granted context, otherwise resolution is denied. This spec covers AC-3 (resolve-by-role, data-driven), AC-4 (AOP allow/deny), and AC-5 (the special `Trusted` security level gating).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SFM |
| Category | Infrastructure |
| Status | Draft |
| Requirements | doc/04_architecture/language/simple_feature_module.md |
| Design | doc/05_design/simple_feature_module.md |
| Source | `test/03_system/feature/sfm/sfm_di_authz_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Exposed layers are linked to an app through data-driven dependency injection
(`register_layers` loops the manifest — no hard-coded wiring) and resolved by role
(`resolve_layer`). Layer access is guarded by an AOP Around interceptor that enforces
the module's security level: `Trusted`/privileged layers require a granted context,
otherwise resolution is denied. This spec covers AC-3 (resolve-by-role, data-driven),
AC-4 (AOP allow/deny), and AC-5 (the special `Trusted` security level gating).

## Key Concepts

| Concept | Description |
|---------|-------------|
| register_layers | Binds every manifest layer to its role-keyed factory (data-driven) |
| resolve_layer | Resolves a layer by role, applying the authorization aspect |
| AuthzContext | Caller identity: principal + whether trusted access is granted |
| make_authz_aspect | Around advice enforcing the module's security level |
| SfmSecurityLevel | `Ordinary` vs the special `Trusted` privileged marker |

## Related Specifications

- [sfm_codec_spec.spl](sfm_codec_spec.spl) — manifest model these layers come from

## Scenarios

### SFM dependency injection

### AC-3: resolve a layer by role from a loaded manifest

#### should resolve a registered ordinary layer by its role

- should resolve a registered ordinary layer by its role
   - API capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should resolve a registered ordinary layer by its role")
val m = ordinary_manifest()
val c = register(m)
match resolve_layer(c, "cli", untrusted_ctx()):
    Ok(_):  assert_true(true)
    Err(e): expect("resolve failed: " + e).to_equal("ok")
```

</details>

#### should fail to resolve a role that is not in the manifest

- should fail to resolve a role that is not in the manifest
   - API capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should fail to resolve a role that is not in the manifest")
val m = ordinary_manifest()
val c = register(m)
match resolve_layer(c, "missing", untrusted_ctx()):
    Ok(_):  expect("should not resolve unknown role").to_equal("ok")
    Err(_): assert_true(true)
```

</details>

#### should wire layers data-driven from the manifest (count matches)

- should wire layers data-driven from the manifest (count matches)
   - API capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should wire layers data-driven from the manifest (count matches)")
# Manifest with two distinct roles -> both resolvable, no hard-coding.
val cli = LayerDescriptor(role: "cli", kind: LayerKind.FrontArgParser, entry_symbol: "a", privileged: false)
val tui = LayerDescriptor(role: "ui", kind: LayerKind.FrontTui, entry_symbol: "b", privileged: false)
val m = FeatureManifest(name: "two", version: "1.0.0", security_level: SfmSecurityLevel.Ordinary, layers: [cli, tui])
val c = register(m)
match resolve_layer(c, "cli", untrusted_ctx()):
    Ok(_):  assert_true(true)
    Err(e): expect("cli failed: " + e).to_equal("ok")
match resolve_layer(c, "ui", untrusted_ctx()):
    Ok(_):  assert_true(true)
    Err(e): expect("ui failed: " + e).to_equal("ok")
```

</details>

### SFM AOP authorization

### AC-4: interceptor enforces access (allow / deny)

#### should allow access to an ordinary layer without a trusted grant

- should allow access to an ordinary layer without a trusted grant
   - API capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should allow access to an ordinary layer without a trusted grant")
match authorize(SfmSecurityLevel.Ordinary,
                LayerDescriptor(role: "cli", kind: LayerKind.FrontArgParser, entry_symbol: "a", privileged: false),
                untrusted_ctx()):
    Ok(_):  assert_true(true)
    Err(e): expect("should allow: " + e).to_equal("ok")
```

</details>

#### should deny access to a privileged layer without a trusted grant

- should deny access to a privileged layer without a trusted grant
   - API capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should deny access to a privileged layer without a trusted grant")
match authorize(SfmSecurityLevel.Trusted,
                LayerDescriptor(role: "device", kind: LayerKind.BackHw, entry_symbol: "hw_open", privileged: true),
                untrusted_ctx()):
    Ok(_):  expect("should have denied").to_equal("ok")
    Err(_): assert_true(true)
```

</details>

#### should allow access to a privileged layer with a trusted grant

- should allow access to a privileged layer with a trusted grant
   - API capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should allow access to a privileged layer with a trusted grant")
match authorize(SfmSecurityLevel.Trusted,
                LayerDescriptor(role: "device", kind: LayerKind.BackHw, entry_symbol: "hw_open", privileged: true),
                trusted_ctx()):
    Ok(_):  assert_true(true)
    Err(e): expect("should allow: " + e).to_equal("ok")
```

</details>

#### should deny resolve_layer of a privileged layer for an untrusted caller

- should deny resolve_layer of a privileged layer for an untrusted caller
   - API capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should deny resolve_layer of a privileged layer for an untrusted caller")
val m = trusted_manifest()
val c = register(m)
match resolve_layer(c, "device", untrusted_ctx()):
    Ok(_):  expect("should have been denied by aspect").to_equal("ok")
    Err(_): assert_true(true)
```

</details>

#### should resolve a privileged layer for a trusted caller

- should resolve a privileged layer for a trusted caller
   - API capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should resolve a privileged layer for a trusted caller")
val m = trusted_manifest()
val c = register(m)
match resolve_layer(c, "device", trusted_ctx()):
    Ok(_):  assert_true(true)
    Err(e): expect("should allow trusted: " + e).to_equal("ok")
```

</details>

### SFM special security level

### AC-5: Trusted is distinct from Ordinary and gates privilege

#### should build an authz aspect bound to the trusted level

- should build an authz aspect bound to the trusted level
   - API capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should build an authz aspect bound to the trusted level")
# Constructing the aspect must succeed; it is the gate for AC-4.
val aspect = make_authz_aspect(SfmSecurityLevel.Trusted)
expect(aspect.name).to_contain("authz")
```

</details>

#### should treat an ordinary module's privileged claim as ungated

- should treat an ordinary module's privileged claim as ungated


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should treat an ordinary module's privileged claim as ungated")
# An Ordinary module cannot enforce trusted gating: a privileged
# layer under Ordinary level resolves for any caller (no marker).
match authorize(SfmSecurityLevel.Ordinary,
                LayerDescriptor(role: "x", kind: LayerKind.BackHw, entry_symbol: "x", privileged: true),
                untrusted_ctx()):
    Ok(_):  assert_true(true)
    Err(e): expect("ordinary should not gate: " + e).to_equal("ok")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/04_architecture/language/simple_feature_module.md`
- **Design:** `doc/05_design/simple_feature_module.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dca74f6565deb47e5564af5148157f95dee9acf56adefd07350caf71c22142dd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dca74f6565deb47e5564af5148157f95dee9acf56adefd07350caf71c22142dd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dca74f6565deb47e5564af5148157f95dee9acf56adefd07350caf71c22142dd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/feature/sfm/sfm_di_authz_spec.spl
mirror: doc/06_spec/03_system/feature/sfm/sfm_di_authz_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/sfm/sfm_di_authz_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/sfm/sfm_di_authz_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/sfm/sfm_di_authz_spec.spl:110:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should resolve a registered ordinary layer by its role' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/sfm/sfm_di_authz_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should resolve a registered ordinary layer by its role' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/sfm/sfm_di_authz_spec.spl:120:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fail to resolve a role that is not in the manifest' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/sfm/sfm_di_authz_spec.spl:120:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should fail to resolve a role that is not in the manifest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/sfm/sfm_di_authz_spec.spl:130:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should wire layers data-driven from the manifest (count matches)' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/sfm/sfm_di_authz_spec.spl:130:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should wire layers data-driven from the manifest (count matches)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/sfm/sfm_di_authz_spec.spl:153:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should allow access to an ordinary layer without a trusted grant' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/sfm/sfm_di_authz_spec.spl:163:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should deny access to a privileged layer without a trusted grant' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/sfm/sfm_di_authz_spec.spl:173:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should allow access to a privileged layer with a trusted grant' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
