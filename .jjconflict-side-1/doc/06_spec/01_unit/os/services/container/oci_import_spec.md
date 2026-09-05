# oci_import — "OCI at the edge" adapter Specification

> (§ sys_oci_import) + simpleos_production_host_master_plan §6.3.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# oci_import — "OCI at the edge" adapter Specification

(§ sys_oci_import) + simpleos_production_host_master_plan §6.3.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-CTR-MDSOC-OCI |
| Category | Runtime / OS / Container / OCI import |
| Status | Active |
| Design | doc/04_architecture/os/container/podman_mdsoc_container_arch.md |
| Source | `test/01_unit/os/services/container/oci_import_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

(§ sys_oci_import) + simpleos_production_host_master_plan §6.3.

Absolute-oracle proof that the edge OCI import adapter is FAIL-CLOSED. A
parsed/normalized OciConfigInput is converted to the manager's ContainerSpec
only after the §6.3 safety checks pass; each of the six unsafe inputs is
rejected with its own distinct error string.

Properties proven:
  - benign import: produces a ContainerSpec with the expected root + image
    digest, caps that are a SUBSET of the policy ceiling, and isolated net
    (no raw host-net cap emitted);
  - never amplified: config caps outside the ceiling are dropped; a raw
    host-net cap is stripped even if requested;
  - six rejects, each with its distinct error: (a) `..` traversal,
    (b) raw host bind mount, (c) device node, (d) lifecycle hooks,
    (e) unpack bound exceeded, (f) missing digest;
  - the traversal check is LOAD-BEARING: with it disabled the same malicious
    config imports OK (fail-once proof the reject is caused by the check).

## Scenarios

### oci_import: benign config imports to a safe ContainerSpec

#### produces the expected root, image digest, and isolated net

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- produces the expected root, image digest, and isolated net
   - Expected: r.ok is true
   - Expected: r.spec.root equals `/c1`
   - Expected: r.spec.image_digest equals `sha256:deadbeef`
   - Expected: r.spec.budget equals `8192u64`
   - Expected: spec_is_isolated_net(r.spec) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("produces the expected root, image digest, and isolated net")
val r = oci_import_checked(benign_input(), oci_policy_default(ceiling()))
expect(r.ok).to_equal(true)
expect(r.spec.root).to_equal("/c1")
expect(r.spec.image_digest).to_equal("sha256:deadbeef")
expect(r.spec.budget).to_equal(8192u64)
# isolated net: the requested raw cap.host_net is NOT emitted.
expect(spec_is_isolated_net(r.spec)).to_equal(true)
```

</details>

#### produced caps are a SUBSET of the policy ceiling (never amplified)

- produced caps are a SUBSET of the policy ceiling (never amplified)
   - Expected: caps_is_subset(r.spec.caps, ceiling()) is true
   - Expected: r.spec.caps.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("produced caps are a SUBSET of the policy ceiling (never amplified)")
val r = oci_import_checked(benign_input(), oci_policy_default(ceiling()))
expect(caps_is_subset(r.spec.caps, ceiling())).to_equal(true)
# the two ceiling-permitted caps survive; host_net was stripped.
expect(r.spec.caps).to_contain("cap.fs_read")
expect(r.spec.caps).to_contain("cap.net_scoped")
expect(r.spec.caps.len()).to_equal(2)
```

</details>

### oci_import: six fail-closed safety checks (§6.3)

#### (a) rejects a mount destination with .. traversal

- (a) rejects a mount destination with .. traversal
   - Expected: r.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("(a) rejects a mount destination with .. traversal")
var inp = benign_input()
inp.mounts = [OciMount(src: "tmpfs", dest: "/tmp/../../etc", mtype: "tmpfs")]
val r = oci_import_checked(inp, oci_policy_default(ceiling()))
expect(r.ok).to_equal(false)
expect(r.error).to_contain("escapes container root")
```

</details>

#### (b) rejects a raw host bind mount when allow_host_mounts=false

- (b) rejects a raw host bind mount when allow_host_mounts=false
   - Expected: r.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("(b) rejects a raw host bind mount when allow_host_mounts=false")
var inp = benign_input()
inp.mounts = [OciMount(src: "/host/etc", dest: "/etc", mtype: "bind")]
val r = oci_import_checked(inp, oci_policy_default(ceiling()))
expect(r.ok).to_equal(false)
expect(r.error).to_contain("raw host bind mount")
```

</details>

#### (c) rejects a device node mount when allow_devices=false

- (c) rejects a device node mount when allow_devices=false
   - Expected: r.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("(c) rejects a device node mount when allow_devices=false")
var inp = benign_input()
inp.mounts = [OciMount(src: "/dev/sda", dest: "/dev/sda", mtype: "device")]
val r = oci_import_checked(inp, oci_policy_default(ceiling()))
expect(r.ok).to_equal(false)
expect(r.error).to_contain("device node mount")
```

</details>

#### (d) rejects lifecycle hooks when allow_hooks=false

- (d) rejects lifecycle hooks when allow_hooks=false
   - Expected: r.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("(d) rejects lifecycle hooks when allow_hooks=false")
var inp = benign_input()
inp.hooks_present = true
val r = oci_import_checked(inp, oci_policy_default(ceiling()))
expect(r.ok).to_equal(false)
expect(r.error).to_contain("lifecycle hooks")
```

</details>

#### (e) rejects an unpack size over the policy bound

- (e) rejects an unpack size over the policy bound
   - Expected: r.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("(e) rejects an unpack size over the policy bound")
var inp = benign_input()
inp.unpack_size = 9999999999u64
val r = oci_import_checked(inp, oci_policy_default(ceiling()))
expect(r.ok).to_equal(false)
expect(r.error).to_contain("unpack size/count")
```

</details>

#### (f) rejects a missing digest when require_digest=true

- (f) rejects a missing digest when require_digest=true
   - Expected: r.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("(f) rejects a missing digest when require_digest=true")
var inp = benign_input()
inp.digest = ""
val r = oci_import_checked(inp, oci_policy_default(ceiling()))
expect(r.ok).to_equal(false)
expect(r.error).to_contain("missing or empty content digest")
```

</details>

### oci_import: policy ceilings widen deliberately

#### a raw host bind mount is admitted when allow_host_mounts=true

- a raw host bind mount is admitted when allow_host_mounts=true
   - Expected: r.ok is true
   - Expected: r.spec.root equals `/c1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("a raw host bind mount is admitted when allow_host_mounts=true")
var inp = benign_input()
inp.mounts = [OciMount(src: "/host/data", dest: "/data", mtype: "bind")]
var pol = oci_policy_default(ceiling())
pol.allow_host_mounts = true
val r = oci_import_checked(inp, pol)
expect(r.ok).to_equal(true)
expect(r.spec.root).to_equal("/c1")
```

</details>

### oci_import: the traversal check is load-bearing (fail-once proof)

#### the SAME malicious config imports OK once the .. check is disabled

- the SAME malicious config imports OK once the .. check is disabled
   - Expected: r.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("the SAME malicious config imports OK once the .. check is disabled")
var inp = benign_input()
inp.mounts = [OciMount(src: "tmpfs", dest: "/tmp/../../etc", mtype: "tmpfs")]
# With check_traversal=false the reject disappears — proving the (a)
# test above fails when the check is removed, then is restored.
val r = oci_import_checked_ex(inp, oci_policy_default(ceiling()), false)
expect(r.ok).to_equal(true)
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

- **Design:** `doc/04_architecture/os/container/podman_mdsoc_container_arch.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2e5d55e6d4f4b3b4c288a14e82454780efee9db11ff176d12ff4097004b04a80`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2e5d55e6d4f4b3b4c288a14e82454780efee9db11ff176d12ff4097004b04a80`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2e5d55e6d4f4b3b4c288a14e82454780efee9db11ff176d12ff4097004b04a80`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/services/container/oci_import_spec.spl
mirror: doc/06_spec/01_unit/os/services/container/oci_import_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/services/container/oci_import_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/container/oci_import_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/services/container/oci_import_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/services/container/oci_import_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces the expected root, image digest, and isolated net' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/container/oci_import_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produced caps are a SUBSET of the policy ceiling (never amplified)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/container/oci_import_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '(a) rejects a mount destination with .. traversal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
