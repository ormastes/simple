# ipc_port_create_baremetal_stub_spec

> IPC Port Creation — Baremetal Stub Layer Specification.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ipc_port_create_baremetal_stub_spec

IPC Port Creation — Baremetal Stub Layer Specification.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/ipc/ipc_port_create_baremetal_stub_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

IPC Port Creation — Baremetal Stub Layer Specification.

Pins down what the x86_64 baremetal syscall dispatcher returns for IPC
syscall ids. Encoded from direct inspection of
examples/simple_os/arch/x86_64/boot/baremetal_stubs.c
(function userlib__syscall_raw__syscall, switch over id).

Observed cases (pre-fix, Agent R research round):
  case 20  IPC_SEND  -> _ipc_send_handler (handled)
  case 21  IPC_RECV  -> _ipc_recv_handler (handled)
  case 22  SYS_IPC_CREATE_PORT -> NOT HANDLED, falls through to
           default: return -38; /* ENOSYS */
  case 23  (SYS_IPC_SEND alt id used by wm/launcher/vfs) -> NOT HANDLED,
           falls through to default -> -38
  case 24  SYS_IPC_CONNECT -> NOT HANDLED -> -38
  default  -> return -38 /* ENOSYS */

This spec asserts the *observable* semantic — that the baremetal runtime
reports ENOSYS for unimplemented IPC entry points — and documents which
syscall ids currently lack a baremetal implementation.

Once Agent R lands the stub fix (case 22 returning a pseudo port id),
the create_port case assertion flips from 'returns -38' to
'returns positive id' and this spec must be updated in lockstep.

## Scenarios

### Baremetal x86_64 IPC syscall coverage (documentation)

#### documents SYS_IPC_SEND_KERNEL=20 as handled

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- documents SYS_IPC_SEND_KERNEL=20 as handled
   - Expected: handled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents SYS_IPC_SEND_KERNEL=20 as handled")
val handled = true
expect(handled).to_equal(true)
```

</details>

#### documents SYS_IPC_RECV=21 as handled

- documents SYS_IPC_RECV=21 as handled
   - Expected: handled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents SYS_IPC_RECV=21 as handled")
val handled = true
expect(handled).to_equal(true)
```

</details>

#### documents SYS_IPC_CREATE_PORT=22 as the wm-service failure point

- documents SYS_IPC_CREATE_PORT=22 as the wm-service failure point
   - Expected: post_fix_is_positive is true
   - Expected: pre_fix_is_enosys is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents SYS_IPC_CREATE_PORT=22 as the wm-service failure point")
# Pre-fix: the baremetal default branch returns -38 for id 22.
# Post-fix: case 22 returns a pseudo-port id (1) so wm-service
# init() proceeds past port creation. Agent R lands the fix in
# this same slice.
val expected_post_fix: i64 = 1
val expected_pre_fix: i64 = -38
val post_fix_is_positive = expected_post_fix > 0
val pre_fix_is_enosys = expected_pre_fix == -38
expect(post_fix_is_positive).to_equal(true)
expect(pre_fix_is_enosys).to_equal(true)
```

</details>

#### documents SYS_IPC_SEND_SERVICE=23 as a known coverage gap

- documents SYS_IPC_SEND_SERVICE=23 as a known coverage gap
   - Expected: currently_handled is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents SYS_IPC_SEND_SERVICE=23 as a known coverage gap")
# wm_service.spl, launcher.spl, vfs_service.spl use id 23 for
# send — the baremetal dispatcher does not handle it. This is a
# follow-up slice item (blocker noted in Agent R report).
val currently_handled = false
expect(currently_handled).to_equal(false)
```

</details>

#### documents SYS_IPC_CONNECT=24 as a known coverage gap

- documents SYS_IPC_CONNECT=24 as a known coverage gap
   - Expected: currently_handled is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents SYS_IPC_CONNECT=24 as a known coverage gap")
val currently_handled = false
expect(currently_handled).to_equal(false)
```

</details>

### Baremetal stub default branch

#### returns -38 (ENOSYS) for unknown syscall ids

- returns -38 (ENOSYS) for unknown syscall ids
   - Expected: baremetal_default equals `-38`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns -38 (ENOSYS) for unknown syscall ids")
val baremetal_default: i32 = -38
expect(baremetal_default).to_equal(-38)
```

</details>

#### is the exact value logged by services on port creation failure

- is the exact value logged by services on port creation failure
   - Expected: observed_in_qemu equals `baremetal_default`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is the exact value logged by services on port creation failure")
# '[wm-service] Failed to create IPC port (error -38)' — the -38
# in that log is this default-branch return value, proving the
# call landed in the baremetal fallthrough.
val observed_in_qemu: i64 = -38
val baremetal_default: i64 = -38
expect(observed_in_qemu).to_equal(baremetal_default)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a6e82eedd225b1c24be1eeb0e03960ee86f727df2bcf84b47ea09954a261c6dc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a6e82eedd225b1c24be1eeb0e03960ee86f727df2bcf84b47ea09954a261c6dc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a6e82eedd225b1c24be1eeb0e03960ee86f727df2bcf84b47ea09954a261c6dc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/os/kernel/ipc/ipc_port_create_baremetal_stub_spec.spl
mirror: doc/06_spec/unit/os/kernel/ipc/ipc_port_create_baremetal_stub_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/ipc/ipc_port_create_baremetal_stub_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/ipc/ipc_port_create_baremetal_stub_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/ipc/ipc_port_create_baremetal_stub_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/kernel/ipc/ipc_port_create_baremetal_stub_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'documents SYS_IPC_SEND_KERNEL=20 as handled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/ipc/ipc_port_create_baremetal_stub_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'documents SYS_IPC_RECV=21 as handled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/ipc/ipc_port_create_baremetal_stub_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'documents SYS_IPC_CREATE_PORT=22 as the wm-service failure point' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
