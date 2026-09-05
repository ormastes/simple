# Board Vulkan Host Provider Inventory (lane L4)

> The sibling SoC lanes (glslang, Mesa enumeration, lavapipe) each build a

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Board Vulkan Host Provider Inventory (lane L4)

The sibling SoC lanes (glslang, Mesa enumeration, lavapipe) each build a

## At a Glance

| Field | Value |
|-------|-------|
| Category | OS / GPU driver |
| Status | In Progress |
| Plan | doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md |
| Source | `test/01_unit/os/vulkan/provider_inventory_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

The sibling SoC lanes (glslang, Mesa enumeration, lavapipe) each build a
descriptor for one open-source Vulkan counterpart. This spec exercises the
foundation they all stand on: the pinned inventory of every open-source
Vulkan-adjacent provider actually installed on this host, and the
independence-grouping rule that decides whether a selection of providers is
real differential evidence or one implementation wearing several ICD names.

The reader here is an engineer asking: *is this identity real, and are these
six drivers actually six references, or one?*

## Scope and Preconditions

No GPU submission and no board are needed to run this file. It exercises pure
data: `ProviderManifest` records built from host measurements taken with
`sha256sum`, `dpkg -l`, `--version`, and `nvidia-smi`, and the counting
predicate over `independence_group`.

## Primary Workflow

Read the measured inventory, confirm every manifest passes the frozen
`provider_manifest_rejections` gate, then confirm the independence predicate
correctly collapses an all-Mesa selection to one reference and correctly
counts NVIDIA's proprietary driver as a second, genuinely independent one.

## Key Concepts

| Concept | Description |
|---------|-------------|
| independence_group | What stops two wrappers over one engine from counting as two references |
| mesa | anv, lavapipe, radv, nouveau, asahi, venus-guest — one upstream tree |
| nvidia-proprietary | The only genuinely independent second reference on this host |
| artifact_hash | A real sha256 of the pinned library, never a placeholder |

## Related Specifications

- [Board vulkan counterpart plan](board_vulkan_counterpart_plan_spec.spl) — how a SoC lane consumes a counterpart

## Evidence and Provenance

Executable against `src/os/drivers/gpu/board_vulkan/provider_inventory.spl`.
The refusal scenarios at the end are the reason this file exists, and they
prove two different things on purpose: the empty-hash gate and the ABI-version
gate genuinely reject a bad manifest; the third scenario proves the OPPOSITE
for `independence_group` — that field is an unverified declaration today, and
a relabelled manifest silently inflates the independent-reference count with
nothing to catch it. That gap is filed as
`doc/08_tracking/bug/board_vulkan_independence_group_is_unverified_declaration_2026-08-11.md`
rather than papered over.

## Recovery and Troubleshooting

A failure naming a provider means that manifest's measured identity is
incomplete or wrong — remeasure it on the host, never invent a replacement
value.

## Compatibility and Limitations

virglrenderer/vtest (the host-side venus transport) was not found installed
on this host as of this measurement and is therefore not in the inventory —
recorded as unavailable rather than guessed. See `VIRGLRENDERER_NOTE`.

`independence_group` is a hand-authored declaration, not derived from the host
— see the bug filed above. Every value in THIS file's inventory was manually
cross-checked against `dpkg -S <pinned .so>` at authoring time (all six Mesa
libraries resolve to package `mesa-vulkan-drivers`; glslang resolves to
`glslang-tools`), but nothing enforces that check for a future edit.

## Scenarios

### board vulkan host provider inventory

#### measures at least seven real providers on this host

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
# @req REQ-BOARD-VULKAN-001
```

</details>

#### accepts every measured provider as a well-formed manifest

- run the frozen rejection gate over the whole inventory


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("run the frozen rejection gate over the whole inventory")
assert_equal(provider_inventory_rejections().len(), 0)
```

</details>

#### groups every Mesa-built driver under one independence_group

- read the independence_group of each Mesa driver


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("read the independence_group of each Mesa driver")
assert_equal(provider_anv().independence_group, INDEPENDENCE_GROUP_MESA)
assert_equal(provider_lavapipe().independence_group, INDEPENDENCE_GROUP_MESA)
assert_equal(provider_radv().independence_group, INDEPENDENCE_GROUP_MESA)
assert_equal(provider_nouveau().independence_group, INDEPENDENCE_GROUP_MESA)
assert_equal(provider_asahi().independence_group, INDEPENDENCE_GROUP_MESA)
assert_equal(provider_venus_guest().independence_group, INDEPENDENCE_GROUP_MESA)
```

</details>

#### counts six Mesa drivers selected together as exactly one independent reference

- select every Mesa driver and count


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("select every Mesa driver and count")
val selection = [
    provider_anv(),
    provider_lavapipe(),
    provider_radv(),
    provider_nouveau(),
    provider_asahi(),
    provider_venus_guest()
]
assert_equal(provider_inventory_independent_reference_count(selection), 1)
```

</details>

#### counts NVIDIA proprietary alongside Mesa as two independent references

- add the one genuinely independent second reference on this host


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("add the one genuinely independent second reference on this host")
val selection = [provider_anv(), provider_lavapipe(), provider_nvidia_proprietary()]
assert_equal(provider_inventory_independent_reference_count(selection), 2)
```

</details>

#### counts glslang, Mesa, and NVIDIA as three independent references

- select one provider from each upstream


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("select one provider from each upstream")
val selection = [provider_anv(), provider_glslang(), provider_nvidia_proprietary()]
assert_equal(provider_inventory_independent_reference_count(selection), 3)
```

</details>

#### pins real measured identity, never a placeholder

- check hash and version are non-empty and version is not a sentinel


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("check hash and version are non-empty and version is not a sentinel")
for manifest in provider_inventory_all():
    assert_true(manifest.artifact_hash.starts_with("sha256:"))
    assert_true(manifest.version != "")
    assert_true(manifest.version != "unknown")
    assert_true(manifest.license_spdx != "")
```

</details>

### board vulkan host provider inventory — sabotage proofs

#### rejects a manifest with an empty artifact_hash

- build a manifest that copies a real provider but blanks the hash


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("build a manifest that copies a real provider but blanks the hash")
val sabotaged = ProviderManifest(
    provider_id: "sabotage-empty-hash",
    provider_kind: ProviderKind.native_isolated_worker,
    independence_group: INDEPENDENCE_GROUP_MESA,
    abi_version: COUNTERPART_ABI_VERSION,
    version: "25.2.8-0ubuntu0.24.04.2",
    artifact_hash: "",
    license_spdx: "MIT",
    components: [bad_component()]
)
val failures = provider_manifest_rejections(sabotaged)
assert_true(failures.len() > 0)
assert_contains(failures.join(";"), "artifact_hash is empty")
```

</details>

#### rejects a manifest with the wrong abi_version

- build a manifest that copies a real provider but bumps abi_version


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("build a manifest that copies a real provider but bumps abi_version")
val sabotaged = ProviderManifest(
    provider_id: "sabotage-bad-abi",
    provider_kind: ProviderKind.native_isolated_worker,
    independence_group: INDEPENDENCE_GROUP_MESA,
    abi_version: COUNTERPART_ABI_VERSION + 1,
    version: "25.2.8-0ubuntu0.24.04.2",
    artifact_hash: "sha256:9ecefd82942c76e227075e01a6dc78318cbb210e7fd86d2bde145501539422e4",
    license_spdx: "MIT",
    components: [bad_component()]
)
val failures = provider_manifest_rejections(sabotaged)
assert_true(failures.len() > 0)
assert_contains(failures.join(";"), "abi_version=")
```

</details>

#### does NOT catch a relabelled lavapipe — independence_group is an unverified declaration

- relabel lavapipe's independence_group away from mesa, changing nothing else
- the frozen rejection gate does not notice: it only checks the field is non-empty
- the honest count for an all-Mesa selection is 1
- mixing in the relabelled manifest silently inflates the count to 2 — undetected
- step


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("relabel lavapipe's independence_group away from mesa, changing nothing else")
val faked_lavapipe = ProviderManifest(
    provider_id: provider_lavapipe().provider_id,
    provider_kind: provider_lavapipe().provider_kind,
    independence_group: "lavapipe-pretends-independent",
    abi_version: provider_lavapipe().abi_version,
    version: provider_lavapipe().version,
    artifact_hash: provider_lavapipe().artifact_hash,
    license_spdx: provider_lavapipe().license_spdx,
    components: provider_lavapipe().components
)
step("the frozen rejection gate does not notice: it only checks the field is non-empty")
assert_equal(provider_manifest_rejections(faked_lavapipe).len(), 0)
step("the honest count for an all-Mesa selection is 1")
val honest_selection = [provider_anv(), provider_radv(), provider_lavapipe()]
assert_equal(provider_inventory_independent_reference_count(honest_selection), 1)
step("mixing in the relabelled manifest silently inflates the count to 2 — undetected")
val selection = [provider_anv(), provider_radv(), faked_lavapipe]
assert_equal(provider_inventory_independent_reference_count(selection), 2)
step(
    "this is the failure independence_group exists to prevent, demonstrated as an "
    + "open gap (doc/08_tracking/bug/board_vulkan_independence_group_is_unverified_"
    + "declaration_2026-08-11.md), not as a caught sabotage — nothing in this module "
    + "or in provider_manifest_rejections derives or verifies independence_group "
    + "against the host today"
)
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

- **Plan:** `doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-BOARD-VULKAN-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fed33da4408ec8f2b0190bd628cc52e5571578727d21ea39d0eb7efc906f325a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fed33da4408ec8f2b0190bd628cc52e5571578727d21ea39d0eb7efc906f325a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fed33da4408ec8f2b0190bd628cc52e5571578727d21ea39d0eb7efc906f325a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/os/vulkan/provider_inventory_spec.spl
mirror: doc/06_spec/01_unit/os/vulkan/provider_inventory_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=75
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/vulkan/provider_inventory_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/01_unit/os/vulkan/provider_inventory_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/os/vulkan/provider_inventory_spec.spl:128:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'measures at least seven real providers on this host' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/vulkan/provider_inventory_spec.spl:136:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts every measured provider as a well-formed manifest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/provider_inventory_spec.spl:140:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'groups every Mesa-built driver under one independence_group' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/provider_inventory_spec.spl:149:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'counts six Mesa drivers selected together as exactly one independent reference' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
