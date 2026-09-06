# PID1 terminal dependency containment policy

> PID1 owns a fixed topological bootstrap chain: VFS, then net, then HTTP. A provider may restart transiently without stopping its clients, but once its restart budget is exhausted its clients must not continue against a dead dependency. This specification proves the pure reverse-dependency selection used by the live service manager before it invokes the PID1-only stop ABI.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# PID1 terminal dependency containment policy

PID1 owns a fixed topological bootstrap chain: VFS, then net, then HTTP. A provider may restart transiently without stopping its clients, but once its restart budget is exhausted its clients must not continue against a dead dependency. This specification proves the pure reverse-dependency selection used by the live service manager before it invokes the PID1-only stop ABI.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Requirements | doc/02_requirements/feature/simple_os_enhance.md |
| Plan | doc/03_plan/sys_test/simple_os_enhance.md |
| Design | doc/05_design/simple_os_enhance.md |
| Research | doc/01_research/local/simple_os_enhance.md |
| Source | `test/01_unit/os/services/init/service_dependency_policy_spec.spl` |
| Updated | 2026-08-11 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

PID1 owns a fixed topological bootstrap chain: VFS, then net, then HTTP. A
provider may restart transiently without stopping its clients, but once its
restart budget is exhausted its clients must not continue against a dead
dependency. This specification proves the pure reverse-dependency selection
used by the live service manager before it invokes the PID1-only stop ABI.

## Requirements

**Requirements:** doc/02_requirements/feature/simple_os_enhance.md

REQ-005 requires a bounded restart policy, quarantine, stale-grant teardown,
and reverse dependency shutdown. This test covers the deterministic selection
part of that requirement; kernel stop, grant teardown and QEMU process evidence
are separate runtime obligations.

## Plan

**Plan:** doc/03_plan/sys_test/simple_os_enhance.md

## Design

**Design:** doc/05_design/simple_os_enhance.md

## Research

**Research:** doc/01_research/local/simple_os_enhance.md

## Syntax

```text
catalog_reverse_dependents_of(failed_index, service_count)
```

The returned indices are highest first, matching reverse dependency shutdown.
For the three-service catalog, a terminal VFS failure selects HTTP then net;
a terminal net failure selects HTTP; terminal HTTP has no dependents.

## Examples

```text
VFS terminal -> [HTTP, net]
net terminal -> [HTTP]
HTTP terminal -> []
```

Invalid bounds yield an empty list. They never produce an arbitrary service
index, so callers cannot accidentally stop a peer or an unrelated workload.

## Evidence boundary

The policy is intentionally side-effect-free. PID1 performs the subsequent
opaque stop calls and kernel-side revocation. A target/QEMU scenario must still
prove that a killed provider causes the selected child processes to stop and
that a transient restart does not prematurely contain them.

## Algorithm

The catalog is intentionally represented in topological order.

The failed provider position is never returned.

No earlier service is returned.

Each later catalog position is a direct or transitive dependent today.

Selection begins at the highest position.

This produces the shutdown order HTTP before net when VFS has failed.

It produces HTTP alone when net has failed.

It produces no selection after HTTP itself has failed.

PID1 receives this list and sends one stop request per still-live target.

The request goes through the opaque root-service ABI.

PID1 then marks those targets quarantined.

Quarantine prevents a dependent from restarting around its unavailable provider.

The list does not encode a restart decision.

Restart decisions remain local to the failed provider's bounded policy.

This distinction allows a healthy dependent to reconnect during a temporary
provider restart.

## Non-goals

This policy does not infer dependencies from endpoint names.

It does not inspect service manifests at runtime.

It does not mint or revoke capabilities.

It does not alter process state directly.

It does not decide whether an exit is transient or terminal.

It does not use timer state or random jitter.

It does not replace the later general dependency-graph supervisor.

The fixed catalog representation is only suitable for the minimal boot chain.

Additional catalog services require an explicit graph policy extension and new
tests before they can rely on this helper.

## Scenarios

### PID1 terminal dependency containment

#### stops HTTP then net when VFS is terminally quarantined

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(catalog_reverse_dependents_of(0, 3)).to_equal([2, 1])
```

</details>

#### stops HTTP when net is terminally quarantined

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(catalog_reverse_dependents_of(1, 3)).to_equal([2])
```

</details>

#### does not contain peers or already-terminal HTTP

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(catalog_reverse_dependents_of(2, 3)).to_equal([])
```

</details>

#### fails closed for invalid catalog bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(catalog_reverse_dependents_of(-1, 3)).to_equal([])
expect(catalog_reverse_dependents_of(3, 3)).to_equal([])
expect(catalog_reverse_dependents_of(0, 0)).to_equal([])
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/simple_os_enhance.md`
- **Plan:** `doc/03_plan/sys_test/simple_os_enhance.md`
- **Design:** `doc/05_design/simple_os_enhance.md`
- **Research:** `doc/01_research/local/simple_os_enhance.md`


</details>
