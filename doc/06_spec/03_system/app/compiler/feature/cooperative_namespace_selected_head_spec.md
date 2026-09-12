<!-- codex-system-test; manual mirror pending pure-Simple spipe-docgen execution -->
# Cooperative namespace and selected-head durability [importance=critical; importance_weight=3]

**Executable suite:** `test/03_system/app/compiler/feature/cooperative_namespace_selected_head_spec.spl`
**Crash matrix fixture:** `test/fixtures/cooperative_namespace_selected_head/recovery_matrix_v1.txt`
**Evidence class:** physical, fresh-independent-process, owner-issued durable recovery evidence.

## Status

All thirteen primary scenarios are deliberately `MissingEvidence`. The current cooperative namespace and selected-head seams refuse before mutation because no host can yet issue one namespace scope spanning blob durability, journal admission, selected-head replacement, directory sync, reader/lease/pin state, and recovery. A DTO, direct filesystem fixture, logical publisher receipt, complete-looking journal, static scan, interpreter load, or Rust seed result is not evidence for this suite. Astra review is required after the host issues the complete receipt; it is not implied by this manual. This matrix proves process-restart behavior only; storage-fault or power-loss durability requires a separately qualified storage-fault provider.

Five supplementary diagnostic controls now call the real frozen components:
the host-prerequisite inventory/name, selected-prefix comparator, writer/head
revalidation, durability-order classifier, and GC issuer refusal. They provide
component-level regression coverage only. They do not validate journal framing
or a typed closure, mint authority, execute a crash, prove independent-process
exclusion, or earn L08 acceptance credit.

Run once the physical host exists, using the qualified self-hosted runtime:

```text
bin/simple test test/03_system/app/compiler/feature/cooperative_namespace_selected_head_spec.spl --native
bin/simple spipe-docgen test/03_system/app/compiler/feature/cooperative_namespace_selected_head_spec.spl --output doc/06_spec --no-index
```

## Primary recovery flow

1. Start from an admitted old selected operation and create one new operation with immutable blobs, an exact checksummed journal prefix, selected head, closure receipt, and rebuildable projection.
2. Inject a real process termination at each matrix row; restart with a new process and a new host/provider instance.
3. Read only the selected-head-bound journal prefix and verify the selected root's typed closure. A complete trailing record is never a recovery root.
4. If recovery resumes the interrupted operation, it must be that exact operation digest and prefix—not merely a generation with equivalent bytes.
5. Independently exercise stale writers, a concurrently started writer process, projection loss, and incomplete namespace GC. Retain host receipt, runtime identity, source/fixture hashes, crash transcript, and Astra review.

## Crash and recovery matrix

| Scenario | Cut point / condition | Required fresh-process result |
|---|---|---|
| L08-NAMESPACE-001 | Before blob sync | Previous selected operation; no admission, head, or projection. |
| L08-NAMESPACE-002 | After blob sync | Blobs may exist but are non-authoritative; previous selection remains. |
| L08-NAMESPACE-003 | Before journal admission | Previous selected operation; no new head/projection. |
| L08-NAMESPACE-004 | After journal admission | Previous selection only; the exact operation may be retained for reissue, never selected without head replacement. |
| L08-NAMESPACE-005 | Before head replace | Journal admission alone cannot change selection. |
| L08-NAMESPACE-006 | After head replace | Coherent old or exact new operation only; indeterminate, never a durable-success acknowledgement. |
| L08-NAMESPACE-007 | Before head directory sync | Coherent old or exact new operation only; indeterminate, never a durable-success acknowledgement. |
| L08-NAMESPACE-008 | After head directory sync | Exact new operation with agreeing head, prefix, closure, and projection. |
| L08-NAMESPACE-009 | Complete trailing record | Record beyond selected prefix remains non-authoritative. |
| L08-NAMESPACE-010 | Stale writer | Refusal; selected head unchanged by the stale request. |
| L08-NAMESPACE-011 | Independent writer process | It cannot publish, abort, or finish the first scope. |
| L08-NAMESPACE-012 | Projection deleted | Rebuild only from selected durable journal/closure evidence. |
| L08-NAMESPACE-013 | Namespace missing a reader/lease/pin | GC refuses; no trash or deletion action. |

## Supplementary component controls

| Scenario | Real component assertion | Non-claim |
|---|---|---|
| L08-NAMESPACE-D01 | The canonical `.simple-cache-selected-head-v1` name is exposed and the physical host prerequisite is closed. | A closed API inventory is not host qualification. |
| L08-NAMESPACE-D02 | A matching selected prefix is returned while arbitrary unselected suffix bytes remain outside it. | Prefix comparison does not validate journal frames, replay, or authorize a journal. |
| L08-NAMESPACE-D03 | Writer-incarnation and whole-head changes return stale diagnostic states. | Diagnostics do not hold a cross-process lock. |
| L08-NAMESPACE-D04 | Pre-replacement, indeterminate, and complete trace states remain distinguishable. | Trace classification does not prove fsync, rename, or power-loss behavior. |
| L08-NAMESPACE-D05 | Incomplete union and complete copied contribution requests both refuse GC authority. | No object is marked, trashed, or deleted by this control. |

## Traceability and admission boundary

| Requirement | Scenarios | Evidence still required |
|---|---:|---|
| REQ-CSM-007 / REQ-CSM-008 | 001–009, 012; D01–D04 supplemental | physical crash harness, selected-head/prefix/closure receipt |
| REQ-CSM-009 | 010–011; D03 supplemental | mutation-scoped CAS plus independent-process exclusion receipt |
| REQ-CSM-012 | 012–013; D05 supplemental | projection-rebuild and complete reader/lease/pin namespace receipt |

The executable file and fixture define structural coverage plus five unadmitted
component controls. Current physical execution state is `U` (unavailable), not
PASS, FAIL, or acceptance credit. If run without the host, the explicit `fail`
is an expected RED failure; it does not retroactively alter this unexecuted
state. Do not use this manual to enable publication, GC, or a default backend
switch.
