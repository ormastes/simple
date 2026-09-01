# Disk Image Bake Specification

> Tests covering SimpleOS target-native image bake admission.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Disk Image Bake Specification

## Scenarios

### SimpleOS target-native image bake admission

#### uses pure-Simple SHA-256 for role artifacts

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses pure-Simple SHA-256 for role artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("uses pure-Simple SHA-256 for role artifacts")
expect(simpleos_role_payload_digest([97u8, 98u8, 99u8])).to_equal(
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
)
```

</details>

#### admits three explicit non-empty role artifacts

- admits three explicit non-empty role artifacts
   - Expected: roles.len() equals `3`
   - Expected: roles[0].role equals `compiler`
   - Expected: roles[1].role equals `interpreter`
   - Expected: roles[2].role equals `loader`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("admits three explicit non-empty role artifacts")
val roles = admitted_roles()
expect(roles.len()).to_equal(3)
expect(roles[0].role).to_equal("compiler")
expect(roles[1].role).to_equal("interpreter")
expect(roles[2].role).to_equal("loader")
expect(roles[0].guest_paths.len()).to_be_greater_than(0)
expect(roles[1].guest_paths.len()).to_be_greater_than(0)
expect(roles[2].guest_paths.len()).to_be_greater_than(0)
```

</details>

#### returns a typed rejection when a role artifact is missing

- returns a typed rejection when a role artifact is missing


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns a typed rejection when a role artifact is missing")
val result = simpleos_admit_role_payloads([
    missing_role_input("compiler", "/artifacts/missing-compiler.smf"),
    role_input("interpreter", "/artifacts/interpreter.smf", valid_smf(2.to_u8())),
    role_input("loader", "/artifacts/loader.smf", valid_smf(3.to_u8())),
])
match result:
    case Ok(_): fail("missing compiler artifact was admitted")
    case Err(error): expect(error).to_equal(SimpleRoleAdmissionError.MissingArtifact)
```

</details>

#### rejects empty artifacts and the general compiler fallback

- rejects empty artifacts and the general compiler fallback


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects empty artifacts and the general compiler fallback")
val empty_result = simpleos_admit_role_payloads([
    role_input("compiler", "/artifacts/empty.smf", []),
    role_input("interpreter", "/artifacts/interpreter.smf", valid_smf(2.to_u8())),
    role_input("loader", "/artifacts/loader.smf", valid_smf(3.to_u8())),
])
match empty_result:
    case Ok(_): fail("empty compiler artifact was admitted")
    case Err(error): expect(error).to_equal(SimpleRoleAdmissionError.EmptyArtifact)

val fallback_result = simpleos_admit_role_payloads([
    role_input("compiler", "/build/simple_simpleos", valid_smf(1.to_u8())),
    role_input("interpreter", "/artifacts/interpreter.smf", valid_smf(2.to_u8())),
    role_input("loader", "/artifacts/loader.smf", valid_smf(3.to_u8())),
])
match fallback_result:
    case Ok(_): fail("general compiler fallback was admitted")
    case Err(error): expect(error).to_equal(SimpleRoleAdmissionError.GeneralPayload)
```

</details>

#### rejects malformed executable bytes before image construction

- rejects malformed executable bytes before image construction


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects malformed executable bytes before image construction")
val result = simpleos_admit_role_payloads([
    role_input("compiler", "/artifacts/malformed.smf", [1.to_u8(), 2.to_u8(), 3.to_u8()]),
    role_input("interpreter", "/artifacts/interpreter.smf", valid_smf(2.to_u8())),
    role_input("loader", "/artifacts/loader.smf", valid_smf(3.to_u8())),
])
match result:
    case Ok(_): fail("malformed executable bytes were admitted")
    case Err(error): expect(error).to_equal(SimpleRoleAdmissionError.InvalidExecutableFormat)
```

</details>

#### rejects duplicate role paths and duplicate artifact digests

- rejects duplicate role paths and duplicate artifact digests


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects duplicate role paths and duplicate artifact digests")
val duplicate_path = simpleos_admit_role_payloads([
    role_input("compiler", "/artifacts/shared.smf", valid_smf(1.to_u8())),
    role_input("interpreter", "/artifacts/shared.smf", valid_smf(2.to_u8())),
    role_input("loader", "/artifacts/loader.smf", valid_smf(3.to_u8())),
])
match duplicate_path:
    case Ok(_): fail("duplicate role path was admitted")
    case Err(error): expect(error).to_equal(SimpleRoleAdmissionError.DuplicatePath)

val duplicate_digest = simpleos_admit_role_payloads([
    role_input("compiler", "/artifacts/compiler.smf", valid_smf(1.to_u8())),
    role_input("interpreter", "/artifacts/other.smf", valid_smf(1.to_u8())),
    role_input("loader", "/artifacts/loader.smf", valid_smf(3.to_u8())),
])
match duplicate_digest:
    case Ok(_): fail("duplicate artifact digest was admitted")
    case Err(error): expect(error).to_equal(SimpleRoleAdmissionError.DuplicateDigest)
```

</details>

#### rejects empty, control, quote, backslash, and noncanonical paths

- rejects empty, control, quote, backslash, and noncanonical paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects empty, control, quote, backslash, and noncanonical paths")
val unsafe_paths: [text] = [
    "",
    " /artifacts/compiler.smf",
    "/artifacts/compiler\"payload.smf",
    "/artifacts/compiler\\payload.smf",
    "/artifacts/compiler\npayload.smf",
    "build/os/../compiler.smf",
    "/artifacts//compiler.smf",
]
for path in unsafe_paths:
    val result = simpleos_admit_role_artifact_path(path)
    match result:
        case Ok(()): fail("unsafe artifact path was admitted: {path}")
        case Err(error): expect(error).to_equal(SimpleRoleAdmissionError.InvalidArtifactPath)
```

</details>

#### fails closed if a manifest role carries an unsafe artifact path

- fails closed if a manifest role carries an unsafe artifact path


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails closed if a manifest role carries an unsafe artifact path")
val roles = admitted_roles()
val unsafe = SimpleRolePayload(
    role: roles[0].role,
    host_path: "/artifacts/compiler\"payload.smf",
    digest: roles[0].digest,
    data: roles[0].data,
    guest_paths: roles[0].guest_paths,
)
val result = simpleos_render_toolchain_manifest([unsafe, roles[1], roles[2]])
match result:
    case Ok(_): fail("unsafe artifact path reached SIMPLETOOL.SDN rendering")
    case Err(error): expect(error).to_equal(SimpleRoleAdmissionError.InvalidArtifactPath)
```

</details>

#### revalidates every caller-constructed manifest role field

- revalidates every caller-constructed manifest role field


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("revalidates every caller-constructed manifest role field")
val roles = admitted_roles()

var forged_role = roles[0]
forged_role.role = "compiler\" } injected"
match simpleos_render_toolchain_manifest([forged_role, roles[1], roles[2]]):
    case Ok(_): fail("forged role reached SIMPLETOOL.SDN rendering")
    case Err(error): expect(error).to_equal(SimpleRoleAdmissionError.UnknownRole)

var forged_digest = roles[0]
forged_digest.digest = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
match simpleos_render_toolchain_manifest([forged_digest, roles[1], roles[2]]):
    case Ok(_): fail("forged digest reached SIMPLETOOL.SDN rendering")
    case Err(error): expect(error).to_equal(SimpleRoleAdmissionError.InvalidDigest)

var forged_guest = roles[0]
forged_guest.guest_paths = ["/bin/simple\" } injected"]
match simpleos_render_toolchain_manifest([forged_guest, roles[1], roles[2]]):
    case Ok(_): fail("forged guest path reached SIMPLETOOL.SDN rendering")
    case Err(error): expect(error).to_equal(SimpleRoleAdmissionError.InvalidGuestPath)
```

</details>

#### renders canonical role, guest path, artifact, and digest bindings

- renders canonical role, guest path, artifact, and digest bindings


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("renders canonical role, guest path, artifact, and digest bindings")
val roles = admitted_roles()
val manifest = match simpleos_render_toolchain_manifest(roles):
    case Ok(value): value
    case Err(_):
        fail("valid role paths were rejected during manifest rendering")
        ""
expect(manifest).to_start_with("simple_toolchain {")
expect(manifest).to_contain("role: \"compiler\"")
expect(manifest).to_contain("role: \"interpreter\"")
expect(manifest).to_contain("role: \"loader\"")
expect(manifest).to_contain("guest_path: \"/bin/simple\"")
expect(manifest).to_contain("guest_path: \"/sys/apps/simple_interpreter\"")
expect(manifest).to_contain("guest_path: \"/sys/apps/simple_loader\"")
expect(manifest).to_contain(roles[0].digest)
expect(manifest).to_contain(roles[1].digest)
expect(manifest).to_contain(roles[2].digest)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/port/disk_image_bake_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS target-native image bake admission.
- SimpleOS target-native image bake admission

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e425a752ae77e19b42d765e011b2d3484f41609c2ff44491d202eb3a070195e7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e425a752ae77e19b42d765e011b2d3484f41609c2ff44491d202eb3a070195e7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e425a752ae77e19b42d765e011b2d3484f41609c2ff44491d202eb3a070195e7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/02_integration/os/port/disk_image_bake_spec.spl
mirror: doc/06_spec/02_integration/os/port/disk_image_bake_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/os/port/disk_image_bake_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/os/port/disk_image_bake_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/os/port/disk_image_bake_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/os/port/disk_image_bake_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses pure-Simple SHA-256 for role artifacts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/os/port/disk_image_bake_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits three explicit non-empty role artifacts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/os/port/disk_image_bake_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns a typed rejection when a role artifact is missing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
