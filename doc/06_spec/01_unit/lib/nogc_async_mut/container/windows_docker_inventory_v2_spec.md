# Windows Docker managed quarantine inventory v2

Status: **NOT_RUN**. No compiler, build, test, native capture or Docker command
was executed. Synthetic decoder vectors are authored specifications, not live
inventory, native ABI, process containment, resource or timing qualification.

Source: `src/lib/nogc_async_mut/container/providers/windows/docker_inventory_v2.spl`.
Specification: `test/01_unit/lib/nogc_async_mut/container/windows_docker_inventory_v2_spec.spl`.

## Read-only observation contract

The inventory helper validates administrator policy and physical/service scope,
then observes actual Windows engine OS, ID and kernel before and after capture.
Only the exact trusted executable, explicit local npipe endpoint, and copied
SystemRoot/TEMP/TMP environment reach the native process facade. Unsupported
hosts/runtimes fail. No script fixture is a production fallback.

`container ls --all --no-trunc` uses the exact provider-label filter and an ID
Go template. Empty output is accepted as an empty observed set; otherwise all
IDs must be full 64-character lowercase hex, unique and at most 64. Every
listed native ID is inspected by exact ID. Listing failure, output truncation,
missing rows, malformed labels and inspection failure reject the entire result.
A second listing rejects observed membership churn; this is not an atomic
snapshot or protection against concurrent external Docker administrators.

Every provider-listed row must carry valid provider, physical-host, service-scope,
service-incarnation, workload, attempt, operation, generation and request labels.
Service mode requires simple.continuity-mode=service-incarnation-v1, a valid
versioned service nonce, and a present but empty simple.boot label. A Go range
presence marker distinguishes missing boot labels from empty map values. The
actual simple.native-machine label must be a canonical lowercase versioned OS
installation GUID. The recorded old scope is reconstructed from physical/service
labels, generation, old native machine, empty actual boot ID and service nonce.
The simple.fence internal token must equal the common
container_scope_fence_id_v2 of that exact old scope; missing or mismatched fences
fail before any foreign-scope filtering. The entry retains native_machine_id and
scope_fence_id separately. The internal fence is never exposed as boot ID.
A different recorded machine remains charged quarantine when its own scope fence
is consistent; the current live machine does not silently filter it away.
Malformed/unscoped legacy rows fail completeness before scope filtering. Valid
other physical/service scopes are excluded after validation and never mutated.

Actual CpuCount and Memory must be canonical positive bounded decimals: at most
256 CPUs and 1 TiB, at least 16 MiB memory. Attempts and generations are positive
canonical signed-64-bit values, with pre-multiplication overflow checks. The
request digest is exactly 64 lowercase hexadecimal characters without a prefix. CPU
ceilings become cpu_millis; memory remains bytes. Created/restarting/running/
removing/paused/exited/dead states all retain their full resource ceilings.
Matching entries are quarantine candidates only. No status, nonce equality,
label observation or empty set grants adoption, readiness, free capacity,
ownership, cleanup permission or journal continuity.

## Bounds and timing limitation

Every stdout/stderr capture is bounded by administrator policy. All process
calls share one 30-second monotonic acceptance budget and each receives at most
its current remaining milliseconds and configured timeout. Clocks are sampled
before/after calls and after final decoding; late/error/backward observations
reject the whole result. There are no retries, sleeps, launches, prune calls or
name-based cleanup.

**This is an acceptance budget, not a hard response deadline.** The existing
process facade can wait for a governor slot before its native timeout starts;
that wait is not preemptible here. An overbudget late return remains failure and
releases no capacity. No claim of return within 30 seconds is made. At most 68
read-only process captures occur (two info, two lists, and up to 64 inspections).

## Authored synthetic coverage

- Empty/exact CRLF ID lists, duplicate/truncated/uppercase/blank IDs, output bound,
  and 64/65 entry boundary.
- Exact inspected ID, separate physical/service scopes, versioned service nonce,
  empty actual boot ID and retained CPU/memory ceilings.
- Missing/malformed/noncanonical native-machine labels, absent/mismatched fence,
  altered physical/service/generation/incarnation fields, and independently
  reconstructed old-machine fences retaining full resource ceilings.
- Missing or malformed labels, field counts, extra rows, output overflow,
  noncanonical/overflowing decimals, absent and exceeded resource bounds.
- Exited/dead entries remain resource charged and are never silently discarded.

Native follow-up, NOT_RUN: use an admitted Windows AOT producer/runtime and
isolated Docker fixture to observe engine bracketing, exact argv/environment,
actual labels/resources, foreign-scope exclusion, failed/missing/legacy rows,
output caps, membership churn and shared-budget failure. A genuine service
restart must quarantine inventory before readiness. Synthetic vectors cannot
prove the Go template, Windows environment capture, governor scheduling or
Docker engine observations.

## Primary references

[Docker container ls](https://docs.docker.com/reference/cli/docker/container/ls/)
documents all-state listing, exact label filtering, no-truncation and ID templates.
[Docker formatting](https://docs.docker.com/engine/cli/formatting/)
documents Go-template output formatting. This source uses escaped literal braces
and passes templates directly as argv; shell quoting is not involved.
