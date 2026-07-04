# Content Authority Specification

> Reader clearance vs content authority level, plus revoked-trust deny.

<!-- sdn-diagram:id=content_authority_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=content_authority_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

content_authority_spec -> std
content_authority_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=content_authority_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Content Authority Specification

Reader clearance vs content authority level, plus revoked-trust deny.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Red (no impl yet) |
| Source | `test/01_unit/lib/common/llm/content_authority_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Reader clearance vs content authority level, plus revoked-trust deny.

## Scenarios

### Content Authority

### release_gate

#### AC-6: reader clearance >= content level → Release

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = ContentAuthority(level: AuthorityLevel.Internal, source_trust: TrustSource.RegistryTrusted)
val decision = release_gate(content, AuthorityLevel.Sensitive)
expect decision.kind to_equal "Release"
```

</details>

#### AC-6: equal clearance → Release

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = ContentAuthority(level: AuthorityLevel.Sensitive, source_trust: TrustSource.RegistryTrusted)
val decision = release_gate(content, AuthorityLevel.Sensitive)
expect decision.kind to_equal "Release"
```

</details>

#### AC-6: reader clearance < content level → Scrub or Block

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = ContentAuthority(level: AuthorityLevel.Secret, source_trust: TrustSource.RegistryTrusted)
val decision = release_gate(content, AuthorityLevel.Public)
val held = (decision.kind == "Scrub") or (decision.kind == "Block")
expect held to_equal true
```

</details>

#### AC-6: revoked trust_source → Block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = ContentAuthority(level: AuthorityLevel.Public, source_trust: TrustSource.Revoked)
val decision = release_gate(content, AuthorityLevel.Secret)
expect decision.kind to_equal "Block"
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


</details>
