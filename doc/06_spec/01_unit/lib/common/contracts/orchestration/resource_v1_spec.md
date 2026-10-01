# resource_v1_spec

> An operator authors an orchestration resource in ordinary SDN. This spec pins the STRICT decode profile: what the canonical parser tolerates and an orchestration document must not. The ordinary parser resolves a duplicate key last-wins; here that is a refusal with a source location. An undeclared field is a refusal, not an extension point. A quantity is canonicalized to an exact integer or refused — never rounded. A platform that cannot provide the requested isolation is refused, never downgraded.

<!-- sdn-diagram:id=resource_v1_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=resource_v1_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

resource_v1_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=resource_v1_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# resource_v1_spec

An operator authors an orchestration resource in ordinary SDN. This spec pins the STRICT decode profile: what the canonical parser tolerates and an orchestration document must not. The ordinary parser resolves a duplicate key last-wins; here that is a refusal with a source location. An undeclared field is a refusal, not an extension point. A quantity is canonicalized to an exact integer or refused — never rounded. A platform that cannot provide the requested isolation is refused, never downgraded.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | doc/01_research/os/container/simple_orchestrator_and_container_2026-09-06.md |
| Source | `test/01_unit/lib/common/contracts/orchestration/resource_v1_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

An operator authors an orchestration resource in ordinary SDN. This spec pins
the STRICT decode profile: what the canonical parser tolerates and an
orchestration document must not. The ordinary parser resolves a duplicate key
last-wins; here that is a refusal with a source location. An undeclared field
is a refusal, not an extension point. A quantity is canonicalized to an exact
integer or refused — never rounded. A platform that cannot provide the
requested isolation is refused, never downgraded.

## Examples

Fixtures under `test/fixtures/orchestration/` are the worked examples:
`echo_deployment.sdn` is the accepted shape; the other four are each a single
deliberate defect (duplicate key, undeclared field, selector/template
mismatch, `native-container` on macos).

Covers LANG-002 (duplicate keys), LANG-003 (unknown fields), LANG-007
(selector/template mismatch) and MAC-003 (macOS refuses native-container)
from the research doc's §14 acceptance catalog.

## Scenarios

### Orchestration resource authoring in SDN

#### accepts the echo Deployment and canonicalizes its quantities to integers

- Read the echo-linux Deployment fixture
- Decode it under the strict profile
- Confirm the object identity and replica intent survived
   - Expected: d.meta.name equals `echo-linux`
   - Expected: d.meta.ns equals `ci`
   - Expected: d.replicas equals `2`
   - Expected: d.selector_labels["app"] equals `echo-linux`
- Confirm the pod template carries one container on the linux native lane
   - Expected: d.template.spec.os_name equals `linux`
   - Expected: d.template.spec.runtime_class equals `native-container`
   - Expected: d.template.spec.network_profile equals `endpoint-v1`
   - Expected: d.template.spec.containers.len() equals `1`
- Confirm the container resolves to a locked artifact set, not an ad-hoc image
   - Expected: c.name equals `echo`
   - Expected: c.artifact_set_ref equals `ci-echo`
   - Expected: c.image equals ``
   - Expected: c.args.len() equals `2`
   - Expected: c.ports[0].name equals `http`
   - Expected: c.ports[0].container_port equals `8080`
- Confirm 250m/1000m became millicores and 64Mi/256Mi became bytes
   - Expected: c.resources.cpu_request_millis equals `250`
   - Expected: c.resources.cpu_limit_millis equals `1000`
   - Expected: c.resources.memory_request_bytes equals `67108864`
   - Expected: c.resources.memory_limit_bytes equals `268435456`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the echo-linux Deployment fixture")
val src = fixture("echo_deployment.sdn")
expect(src).to_contain("kind: Deployment")

step("Decode it under the strict profile")
val d = deployment_of("echo_deployment.sdn")

step("Confirm the object identity and replica intent survived")
expect(d.meta.name).to_equal("echo-linux")
expect(d.meta.ns).to_equal("ci")
expect(d.replicas).to_equal(2)
expect(d.selector_labels["app"]).to_equal("echo-linux")

step("Confirm the pod template carries one container on the linux native lane")
expect(d.template.spec.os_name).to_equal("linux")
expect(d.template.spec.runtime_class).to_equal("native-container")
expect(d.template.spec.network_profile).to_equal("endpoint-v1")
expect(d.template.spec.containers.len()).to_equal(1)

step("Confirm the container resolves to a locked artifact set, not an ad-hoc image")
val c = d.template.spec.containers[0]
expect(c.name).to_equal("echo")
expect(c.artifact_set_ref).to_equal("ci-echo")
expect(c.image).to_equal("")
expect(c.args.len()).to_equal(2)
expect(c.ports[0].name).to_equal("http")
expect(c.ports[0].container_port).to_equal(8080)

step("Confirm 250m/1000m became millicores and 64Mi/256Mi became bytes")
expect(c.resources.cpu_request_millis).to_equal(250)
expect(c.resources.cpu_limit_millis).to_equal(1000)
expect(c.resources.memory_request_bytes).to_equal(67108864)
expect(c.resources.memory_limit_bytes).to_equal(268435456)
```

</details>

#### refuses a duplicate key instead of silently keeping the last one

- Decode a Deployment whose metadata declares name twice
- Confirm the document was refused as a duplicate key, not accepted
   - Expected: r.kind equals `duplicate_key`
   - Expected: r.path equals `metadata.name`
- Confirm the refusal names the offending source line
   - Expected: r.line equals `6`
   - Expected: r.col equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Decode a Deployment whose metadata declares name twice")
val r = rejection_of("duplicate_key.sdn")

step("Confirm the document was refused as a duplicate key, not accepted")
expect(r.kind).to_equal("duplicate_key")
expect(r.path).to_equal("metadata.name")

step("Confirm the refusal names the offending source line")
expect(r.line).to_equal(6)
expect(r.col).to_equal(5)
```

</details>

#### refuses an undeclared field and names its schema path

- Decode a pod template carrying an undeclared nodeSelector field
- Confirm the exact schema path is reported
   - Expected: r.kind equals `unknown_field`
   - Expected: r.path equals `spec.template.spec.nodeSelector`
- Confirm the refusal carries a source location


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Decode a pod template carrying an undeclared nodeSelector field")
val r = rejection_of("unknown_field.sdn")

step("Confirm the exact schema path is reported")
expect(r.kind).to_equal("unknown_field")
expect(r.path).to_equal("spec.template.spec.nodeSelector")
expect(r.message).to_contain("nodeSelector")

step("Confirm the refusal carries a source location")
expect(r.line).to_be_greater_than(0)
```

</details>

#### refuses a Deployment whose selector does not select its own template

- Decode a Deployment whose template label disagrees with the selector
- Confirm the mismatch is refused at the template labels
   - Expected: r.kind equals `selector_template_mismatch`
   - Expected: r.path equals `spec.template.metadata.labels`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Decode a Deployment whose template label disagrees with the selector")
val r = rejection_of("selector_mismatch.sdn")

step("Confirm the mismatch is refused at the template labels")
expect(r.kind).to_equal("selector_template_mismatch")
expect(r.path).to_equal("spec.template.metadata.labels")
```

</details>

#### refuses native-container on macos instead of downgrading the isolation

- Decode a macos pod template that asks for native-container
- Confirm the combination is refused, with the honest alternatives named
   - Expected: r.kind equals `unsupported_os_runtime_class`
   - Expected: r.path equals `spec.template.spec.runtimeClassName`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Decode a macos pod template that asks for native-container")
val r = rejection_of("macos_native_container.sdn")

step("Confirm the combination is refused, with the honest alternatives named")
expect(r.kind).to_equal("unsupported_os_runtime_class")
expect(r.path).to_equal("spec.template.spec.runtimeClassName")
expect(r.message).to_contain("native-sandbox")
```

</details>

#### refuses a kind this contract version does not decode

- Decode a document declaring an undecoded kind
- Confirm the kind is reported as not decoded
   - Expected: r.kind equals `unsupported_kind`
   - Expected: r.path equals `kind`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Decode a document declaring an undecoded kind")
val doc = "apiVersion: " + ORCHESTRATION_API_VERSION_V1 + "\n" +
          "kind: Job\n" +
          "metadata:\n" +
          "    name: build-linux\n" +
          "spec:\n" +
          "    replicas: 1\n"
match decode_resource(doc):
    case Ok(_): assert_true(false)
    case Err(r):
        step("Confirm the kind is reported as not decoded")
        expect(r.kind).to_equal("unsupported_kind")
        expect(r.path).to_equal("kind")
```

</details>

#### refuses an unparseable resource quantity rather than rounding it

- Decode a Pod whose cpu request is not an integer core or millicore value
- Confirm the quantity is refused at its own schema path
   - Expected: r.kind equals `quantity`
   - Expected: r.path equals `spec.containers.0.resources.requests.cpu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Decode a Pod whose cpu request is not an integer core or millicore value")
val doc = "apiVersion: " + ORCHESTRATION_API_VERSION_V1 + "\n" +
          "kind: Pod\n" +
          "metadata:\n" +
          "    name: probe\n" +
          "spec:\n" +
          "    os:\n" +
          "        name: linux\n" +
          "    runtimeClassName: native-container\n" +
          "    containers:\n" +
          "        - name: probe\n" +
          "          image: \"registry.example/probe@sha256:aa\"\n" +
          "          resources:\n" +
          "              requests:\n" +
          "                  cpu: \"0.25\"\n"
match decode_resource(doc):
    case Ok(_): assert_true(false)
    case Err(r):
        step("Confirm the quantity is refused at its own schema path")
        expect(r.kind).to_equal("quantity")
        expect(r.path).to_equal("spec.containers.0.resources.requests.cpu")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Research:** [doc/01_research/os/container/simple_orchestrator_and_container_2026-09-06.md](doc/01_research/os/container/simple_orchestrator_and_container_2026-09-06.md)


</details>

## Generation history

Generated by `simple spipe-docgen` (Simple).
Source SHA-256: `59b90602557f02da7dc6ea8d6d82099bcb68ae79241d94602c1afd0fad4881eb`
