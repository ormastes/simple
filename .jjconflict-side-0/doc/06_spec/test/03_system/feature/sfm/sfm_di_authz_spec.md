# SFM Dependency Injection & AOP Authorization

> Exposed layers are linked to an app through data-driven dependency injection (`register_layers` loops the manifest — no hard-coded wiring) and resolved by role (`resolve_layer`). Layer access is guarded by an AOP Around interceptor that enforces the module's security level: `Trusted`/privileged layers require a granted context, otherwise resolution is denied. This spec covers AC-3 (resolve-by-role, data-driven), AC-4 (AOP allow/deny), and AC-5 (the special `Trusted` security level gating).

<!-- sdn-diagram:id=sfm_di_authz_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sfm_di_authz_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sfm_di_authz_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sfm_di_authz_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

- Ok
   - API capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = ordinary_manifest()
val c = register(m)
match resolve_layer(c, "cli", untrusted_ctx()):
    Ok(_):  assert_true(true)
    Err(e): expect("resolve failed: " + e).to_equal("ok")
```

</details>

#### should fail to resolve a role that is not in the manifest

- Err
   - API capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = ordinary_manifest()
val c = register(m)
match resolve_layer(c, "missing", untrusted_ctx()):
    Ok(_):  expect("should not resolve unknown role").to_equal("ok")
    Err(_): assert_true(true)
```

</details>

#### should wire layers data-driven from the manifest (count matches)

- Ok
   - API capture: after_step
- Ok
   - API capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- LayerDescriptor
   - API capture: after_step
- untrusted ctx
   - API capture: after_step
- Ok
   - API capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match authorize(SfmSecurityLevel.Ordinary,
                LayerDescriptor(role: "cli", kind: LayerKind.FrontArgParser, entry_symbol: "a", privileged: false),
                untrusted_ctx()):
    Ok(_):  assert_true(true)
    Err(e): expect("should allow: " + e).to_equal("ok")
```

</details>

#### should deny access to a privileged layer without a trusted grant

- LayerDescriptor
   - API capture: after_step
- untrusted ctx
   - API capture: after_step
- Err
   - API capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match authorize(SfmSecurityLevel.Trusted,
                LayerDescriptor(role: "device", kind: LayerKind.BackHw, entry_symbol: "hw_open", privileged: true),
                untrusted_ctx()):
    Ok(_):  expect("should have denied").to_equal("ok")
    Err(_): assert_true(true)
```

</details>

#### should allow access to a privileged layer with a trusted grant

- LayerDescriptor
   - API capture: after_step
- trusted ctx
   - API capture: after_step
- Ok
   - API capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match authorize(SfmSecurityLevel.Trusted,
                LayerDescriptor(role: "device", kind: LayerKind.BackHw, entry_symbol: "hw_open", privileged: true),
                trusted_ctx()):
    Ok(_):  assert_true(true)
    Err(e): expect("should allow: " + e).to_equal("ok")
```

</details>

#### should deny resolve_layer of a privileged layer for an untrusted caller

- Err
   - API capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = trusted_manifest()
val c = register(m)
match resolve_layer(c, "device", untrusted_ctx()):
    Ok(_):  expect("should have been denied by aspect").to_equal("ok")
    Err(_): assert_true(true)
```

</details>

#### should resolve a privileged layer for a trusted caller

- Ok
   - API capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

**Scenario capture:** api after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Constructing the aspect must succeed; it is the gate for AC-4.
val aspect = make_authz_aspect(SfmSecurityLevel.Trusted)
expect(aspect.name).to_contain("authz")
```

</details>

#### should treat an ordinary module's privileged claim as ungated

- LayerDescriptor
- untrusted ctx
- Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- **Requirements:** [doc/04_architecture/language/simple_feature_module.md](doc/04_architecture/language/simple_feature_module.md)
- **Design:** [doc/05_design/simple_feature_module.md](doc/05_design/simple_feature_module.md)


</details>
