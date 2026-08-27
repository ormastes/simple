# positioned_backend_composition_v1_spec

> Typed production routing and canonical SOSIX positioned acceptance path.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# positioned_backend_composition_v1_spec

Typed production routing and canonical SOSIX positioned acceptance path.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/sosix/positioned_backend_composition_v1_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Typed production routing and canonical SOSIX positioned acceptance path.

## Scenarios

### SOSIX typed positioned backend composition v1

#### installs the typed owner in the production shim with FAT32 default

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- installs the typed owner in the production shim with FAT32 default


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("installs the typed owner in the production shim with FAT32 default")
val source = rt_file_read_text(
    "src/os/kernel/abi/syscall_shim_positioned.spl") ?? ""
expect(source.contains(
    "g_shim_positioned_backend: SosixPositionedBackendOwnerV1")).to_be(true)
expect(source.contains("sosix_positioned_backend_default_v1()")).to_be(true)
expect(source.contains("shim_positioned_install_backend_route_v1(")).to_be(true)
expect(source.contains(
    "g_shim_positioned_backend = SosixFat32PositionedVfsBackendV1()")).to_be(false)
```

</details>

#### preserves FAT32 default and installs each filesystem by explicit enum

- preserves FAT32 default and installs each filesystem by explicit enum
   - Expected: sosix_positioned_backend_route_name_v1(default_owner) equals `fat32`
   - Expected: default_owner.route_generation equals `1u64`
   - Expected: sosix_positioned_backend_route_name_v1(nvfs.owner) equals `nvfs`
   - Expected: sosix_positioned_backend_route_name_v1(dbfs.owner) equals `dbfs`
   - Expected: sosix_positioned_backend_route_name_v1(fat32.owner) equals `fat32`
   - Expected: fat32.owner.route_generation equals `4u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("preserves FAT32 default and installs each filesystem by explicit enum")
val default_owner = sosix_positioned_backend_default_v1()
expect(sosix_positioned_backend_route_name_v1(default_owner)).to_equal("fat32")
expect(default_owner.route_generation).to_equal(1u64)

val nvfs = sosix_positioned_backend_install_v1(
    default_owner, SosixPositionedBackendKindV1.Nvfs)
val dbfs = sosix_positioned_backend_install_v1(
    nvfs.owner, SosixPositionedBackendKindV1.Dbfs)
val fat32 = sosix_positioned_backend_install_v1(
    dbfs.owner, SosixPositionedBackendKindV1.Fat32)
expect(nvfs.accepted).to_be(true)
expect(sosix_positioned_backend_route_name_v1(nvfs.owner)).to_equal("nvfs")
expect(sosix_positioned_backend_route_name_v1(dbfs.owner)).to_equal("dbfs")
expect(sosix_positioned_backend_route_name_v1(fat32.owner)).to_equal("fat32")
expect(fat32.owner.route_generation).to_equal(4u64)
```

</details>

#### rejects unavailable and exhausted route installs without changing owner

- rejects unavailable and exhausted route installs without changing owner
   - Expected: unavailable.reason equals `positioned-backend-route-unavailable`
   - Expected: unavailable.owner.route_generation equals `1u64`
   - Expected: exhausted.reason equals `positioned-backend-route-generation-exhausted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects unavailable and exhausted route installs without changing owner")
val owner = sosix_positioned_backend_default_v1()
val unavailable = sosix_positioned_backend_install_v1(
    owner, SosixPositionedBackendKindV1.Unavailable)
val exhausted = sosix_positioned_backend_install_v1(
    SosixPositionedBackendOwnerV1(
        kind: SosixPositionedBackendKindV1.Fat32,
        route_generation: 0xffffffffffffffffu64),
    SosixPositionedBackendKindV1.Nvfs)
expect(unavailable.accepted).to_be(false)
expect(unavailable.reason).to_equal("positioned-backend-route-unavailable")
expect(unavailable.owner.route_generation).to_equal(1u64)
expect(exhausted.accepted).to_be(false)
expect(exhausted.reason).to_equal("positioned-backend-route-generation-exhausted")
```

</details>

#### round-trips NVFS through registered syscall dispatch and a virtual object

- round-trips NVFS through registered syscall dispatch and a virtual object
   - Expected: result.reason equals `positioned-acceptance-round-trip`
   - Expected: result.bytes equals `[0u8, 0u8, 11u8, 22u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("round-trips NVFS through registered syscall dispatch and a virtual object")
_clear_vfs_rootfs_for_test()
vfs_mount_rootfs(DriverInstance.Nvfs(NvfsDriver.new("sosix-route"))).unwrap()
val result = sosix_positioned_acceptance_round_trip_v1(
    SosixPositionedBackendKindV1.Nvfs, "/route.bin")
expect(result.accepted).to_be(true)
expect(result.reason).to_equal("positioned-acceptance-round-trip")
expect(result.bytes).to_equal([0u8, 0u8, 11u8, 22u8])
```

</details>

#### does not infer a DBFS route from an NVFS virtual object identity

- does not infer a DBFS route from an NVFS virtual object identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("does not infer a DBFS route from an NVFS virtual object identity")
_clear_vfs_rootfs_for_test()
vfs_mount_rootfs(DriverInstance.Nvfs(NvfsDriver.new("sosix-kind"))).unwrap()
val result = sosix_positioned_acceptance_round_trip_v1(
    SosixPositionedBackendKindV1.Dbfs, "/wrong-kind.bin")
expect(result.accepted).to_be(false)
expect(result.reason).to_contain("dbfs-positioned-unsupported")
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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `217357847e9983af2ebe18113b964bc156b7b79d8faba43083590aac7170080d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `217357847e9983af2ebe18113b964bc156b7b79d8faba43083590aac7170080d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `217357847e9983af2ebe18113b964bc156b7b79d8faba43083590aac7170080d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/sosix/positioned_backend_composition_v1_spec.spl
mirror: doc/06_spec/01_unit/os/sosix/positioned_backend_composition_v1_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/os/sosix/positioned_backend_composition_v1_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/sosix/positioned_backend_composition_v1_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/sosix/positioned_backend_composition_v1_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/os/sosix/positioned_backend_composition_v1_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'installs the typed owner in the production shim with FAT32 default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/sosix/positioned_backend_composition_v1_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves FAT32 default and installs each filesystem by explicit enum' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/sosix/positioned_backend_composition_v1_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unavailable and exhausted route installs without changing owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
