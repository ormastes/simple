# Mir Transfer Operations Specification

> Tests covering WP-12 explicit MIR transfer operations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mir Transfer Operations Specification

## Scenarios

### WP-12 explicit MIR transfer operations

#### serializes stable transfer direction and mode facts

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- serializes stable transfer direction and mode facts


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes stable transfer direction and mode facts")
val json = serialize_mir_inst_kind(MirInstKind.TransferOut(
    LocalId(id: 8), LocalId(id: 7), MirExecutionDomain.Process,
    MirTransferMode.Copy, MirTransferPayload.EncodedCopy, false))
expect(json).to_equal(
    "{\"TransferOut\":{\"dest\":8,\"source\":7,\"destination\":\"process\",\"mode\":\"copy\",\"payload\":\"encoded_copy\",\"runtime_classify\":false}}")
```

</details>

#### treats an owned transfer as source-consuming

- treats an owned transfer as source-consuming


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats an owned transfer as source-consuming")
val source = LocalId(id: 0)
val use_dest = LocalId(id: 1)
val insts = [
    transfer_inst(MirInstKind.TransferOut(
        LocalId(id: 2), source, MirExecutionDomain.Thread,
        MirTransferMode.OwnedMove, MirTransferPayload.OwnedRegion,
        false)),
    transfer_inst(MirInstKind.Copy(use_dest, source))
]
assert_true(transfer_body_has_errors(insts))
```

</details>

#### keeps inline-copy transfer source usable

- keeps inline-copy transfer source usable


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps inline-copy transfer source usable")
val source = LocalId(id: 0)
val use_dest = LocalId(id: 1)
val insts = [
    transfer_inst(MirInstKind.TransferOut(
        LocalId(id: 2), source, MirExecutionDomain.Thread,
        MirTransferMode.Copy, MirTransferPayload.InlineCopy, false)),
    transfer_inst(MirInstKind.Copy(use_dest, source))
]
assert_false(transfer_body_has_errors(insts))
```

</details>

#### initializes received and snapshot destinations

- initializes received and snapshot destinations


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes received and snapshot destinations")
val received = LocalId(id: 0)
val snapshot = LocalId(id: 1)
val insts = [
    transfer_inst(MirInstKind.TransferIn(
        received, MirExecutionDomain.Actor,
        MirTransferMode.OwnedMove, MirTransferPayload.OwnedRegion)),
    transfer_inst(MirInstKind.AcquireSnapshot(snapshot, received)),
    transfer_inst(MirInstKind.Copy(received, snapshot))
]
assert_false(transfer_body_has_errors(insts))
```

</details>

#### consumes committed update ownership

- consumes committed update ownership


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("consumes committed update ownership")
val base = LocalId(id: 0)
val updates = LocalId(id: 1)
val result = LocalId(id: 2)
val later = LocalId(id: 3)
val insts = [
    transfer_inst(MirInstKind.CommitUpdates(
        Some(result), base, updates)),
    transfer_inst(MirInstKind.Copy(later, updates))
]
assert_true(transfer_body_has_errors(insts))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/mir_transfer_operations_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WP-12 explicit MIR transfer operations.
- WP-12 explicit MIR transfer operations

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `359bff9e83c48bfbf9db626153075d4d7c8bdbb100cfc7cf413e8db7991b3a4b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `359bff9e83c48bfbf9db626153075d4d7c8bdbb100cfc7cf413e8db7991b3a4b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `359bff9e83c48bfbf9db626153075d4d7c8bdbb100cfc7cf413e8db7991b3a4b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/mir/mir_transfer_operations_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/mir_transfer_operations_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir/mir_transfer_operations_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/mir_transfer_operations_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/mir_transfer_operations_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'serializes stable transfer direction and mode facts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/mir_transfer_operations_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats an owned transfer as source-consuming' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/mir_transfer_operations_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps inline-copy transfer source usable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
