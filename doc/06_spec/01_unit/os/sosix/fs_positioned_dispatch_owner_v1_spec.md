# fs_positioned_dispatch_owner_v1_spec

> Focused executable contract for value-threaded positioned dispatch ownership.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fs_positioned_dispatch_owner_v1_spec

Focused executable contract for value-threaded positioned dispatch ownership.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/sosix/fs_positioned_dispatch_owner_v1_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused executable contract for value-threaded positioned dispatch ownership.

## Scenarios

### SOSIX positioned dispatcher owner seam v1

#### threads registry mutation and request identity through an injected owner

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- threads registry mutation and request identity through an injected owner
   - Expected: state.result.value equals `1`
   - Expected: state.owner.registry_owner.registry.buffers[0].bytes equals `[20, 0]`
   - Expected: state.owner.next_request_token equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("threads registry mutation and request identity through an injected owner")
val state = sosix_fs_dispatch_positioned_with_owner_v1(
    sosix_fs_positioned_syscall_args_v1(
        SOSIX_FS_PREAD_REGISTERED_V1, 41, 73,
        0x0000000900000004, 1, 0, 1),
    true, 42, _owner(), OwnerBackend(bytes: [10, 20]))

expect(state.accepted).to_be(true)
expect(state.result.value).to_equal(1)
expect(state.owner.registry_owner.registry.buffers[0].bytes).to_equal([20, 0])
expect(state.owner.next_request_token).to_equal(12)
```

</details>

#### fails closed without consuming identity when caller authentication fails

- fails closed without consuming identity when caller authentication fails
   - Expected: state.result.value equals `-13`
   - Expected: state.owner.next_request_token equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails closed without consuming identity when caller authentication fails")
val state = sosix_fs_dispatch_positioned_with_owner_v1(
    sosix_fs_positioned_syscall_args_v1(
        SOSIX_FS_PREAD_REGISTERED_V1, 41, 73,
        0x0000000900000004, 0, 0, 1),
    false, 42, _owner(), OwnerBackend(bytes: [10]))

expect(state.accepted).to_be(false)
expect(state.result.value).to_equal(-13)
expect(state.owner.next_request_token).to_equal(11)
```

</details>

#### fails closed when the injected lifecycle owner is not ready

- fails closed when the injected lifecycle owner is not ready
   - Expected: state.reason equals `positioned-dispatch-owner-not-ready`
   - Expected: state.result.value equals `-95`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails closed when the injected lifecycle owner is not ready")
var owner = _owner()
owner.registry_owner.service_generation = 0
val state = sosix_fs_dispatch_positioned_with_owner_v1(
    SyscallArgs(id: 134, arg0: 41, arg1: 73, arg2: 0,
        arg3: 0, arg4: 0, arg5: 1),
    true, 42, owner, OwnerBackend(bytes: [10]))

expect(state.accepted).to_be(false)
expect(state.reason).to_equal("positioned-dispatch-owner-not-ready")
expect(state.result.value).to_equal(-95)
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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `60aadc3401e060c0d40e27891ee28fd7bd44a282e7b07751c2cdcae473b5bb2b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `60aadc3401e060c0d40e27891ee28fd7bd44a282e7b07751c2cdcae473b5bb2b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `60aadc3401e060c0d40e27891ee28fd7bd44a282e7b07751c2cdcae473b5bb2b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/sosix/fs_positioned_dispatch_owner_v1_spec.spl
mirror: doc/06_spec/01_unit/os/sosix/fs_positioned_dispatch_owner_v1_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/sosix/fs_positioned_dispatch_owner_v1_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/sosix/fs_positioned_dispatch_owner_v1_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/sosix/fs_positioned_dispatch_owner_v1_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/sosix/fs_positioned_dispatch_owner_v1_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'threads registry mutation and request identity through an injected owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/sosix/fs_positioned_dispatch_owner_v1_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed without consuming identity when caller authentication fails' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/sosix/fs_positioned_dispatch_owner_v1_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed when the injected lifecycle owner is not ready' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
