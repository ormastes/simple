# simpleos_deploy_image_simple_toolchain_spec

> Negative image-admission coverage through the production SimpleOS image

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simpleos_deploy_image_simple_toolchain_spec

Negative image-admission coverage through the production SimpleOS image

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_deploy_image_simple_toolchain_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Negative image-admission coverage through the production SimpleOS image
builder. These scenarios prove that unadmitted payloads cannot create
/SYS/SIMPLETOOL.SDN. They do not prove image boot or guest execution.

## Scenarios

### SimpleOS deploy image Simple toolchain payload

#### should reject a marker payload without a provenance stamp

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should reject a marker payload without a provenance stamp
- Submit a marker payload to the production image builder


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject a marker payload without a provenance stamp")
val root = "build/tmp/simpleos_deploy_image_marker_rejection"
dir_create_all(root)
val payload = root + "/simple-target.smf"
val image = root + "/simpleos-disk.img"

step("Submit a marker payload to the production image builder")
expect(file_write(payload, "SMF_FAKE_TARGET_SIMPLE\nrole=compiler-interpreter-loader\n")).to_be(true)
val result = build_install_image_with_simple_binary(PkgArch.X86_64, "", "", image, 64, payload)
expect(result.is_err()).to_be(true)
if val Err(message) = result:
    expect(message).to_contain("lacks target provenance")
expect(file_exists(image + ".contents/rootfs/SYS/SIMPLETOOL.SDN")).to_be(false)
```

</details>

#### should reject payload provenance from the Rust bootstrap seed

- should reject payload provenance from the Rust bootstrap seed
- Submit seed provenance to the production image builder


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject payload provenance from the Rust bootstrap seed")
val root = "build/tmp/simpleos_deploy_image_seed_rejection"
dir_create_all(root)
val payload = root + "/simple"
val image = root + "/simpleos-disk.img"

step("Submit seed provenance to the production image builder")
expect(file_write(payload, "not-an-admitted-elf\n")).to_be(true)
expect(file_write(payload + ".build_stamp",
    "target=x86_64-unknown-simpleos\n" +
    "entry=src/app/simpleos_tool/main.spl\n" +
    "entry_closure=true\n" +
    "compiler=src/compiler_rust/target/bootstrap/simple\n" +
    "backend=llvm\n")).to_be(true)
val result = build_install_image_with_simple_binary(PkgArch.X86_64, "", "", image, 64, payload)
expect(result.is_err()).to_be(true)
if val Err(message) = result:
    expect(message).to_contain("bootstrap seed")
expect(file_exists(image + ".contents/rootfs/SYS/SIMPLETOOL.SDN")).to_be(false)
```

</details>

#### should reject a payload stamped for the wrong target

- should reject a payload stamped for the wrong target
- Submit wrong-target provenance to the production image builder


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject a payload stamped for the wrong target")
val root = "build/tmp/simpleos_deploy_image_target_rejection"
dir_create_all(root)
val payload = root + "/simple"
val image = root + "/simpleos-disk.img"

step("Submit wrong-target provenance to the production image builder")
expect(file_write(payload, "not-an-admitted-elf\n")).to_be(true)
expect(file_write(payload + ".build_stamp",
    "target=aarch64-unknown-simpleos\n" +
    "entry=src/app/simpleos_tool/main.spl\n" +
    "entry_closure=true\n" +
    "compiler=build/bootstrap/stage4/x86_64-unknown-linux-gnu/simple\n" +
    "backend=llvm\n")).to_be(true)
val result = build_install_image_with_simple_binary(PkgArch.X86_64, "", "", image, 64, payload)
expect(result.is_err()).to_be(true)
if val Err(message) = result:
    expect(message).to_contain("target mismatch")
expect(file_exists(image + ".contents/rootfs/SYS/SIMPLETOOL.SDN")).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-004`
- `REQ-007`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `547c38562a86efdec81ebbcf14000184eb5eedf0dc1251b0eba6b67191156505`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `547c38562a86efdec81ebbcf14000184eb5eedf0dc1251b0eba6b67191156505`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `547c38562a86efdec81ebbcf14000184eb5eedf0dc1251b0eba6b67191156505`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/os/simpleos_deploy_image_simple_toolchain_spec.spl
mirror: doc/06_spec/03_system/os/simpleos_deploy_image_simple_toolchain_spec.md (current)
findings: 9 blockers: 1
  narrative=100 structure=85 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/03_system/os/simpleos_deploy_image_simple_toolchain_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/simpleos_deploy_image_simple_toolchain_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/simpleos_deploy_image_simple_toolchain_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/os/simpleos_deploy_image_simple_toolchain_spec.spl:25:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a marker payload without a provenance stamp' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos_deploy_image_simple_toolchain_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject a marker payload without a provenance stamp' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos_deploy_image_simple_toolchain_spec.spl:41:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject payload provenance from the Rust bootstrap seed' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos_deploy_image_simple_toolchain_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject payload provenance from the Rust bootstrap seed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos_deploy_image_simple_toolchain_spec.spl:63:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject a payload stamped for the wrong target' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos_deploy_image_simple_toolchain_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject a payload stamped for the wrong target' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
