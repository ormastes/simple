# Portable BuildRunner loses terminal ownership on V4 capability refusal

Status: fixed in source; interpreter worker/manager regression. Baseline:
release/1.0.0 `7b4220c9e11`. Native Darwin V4 and Hello remain unavailable.

A monitor-policy task reaches the portable worker's V4 capability query before
any executable pin or process start. An unavailable provider (the current
Darwin outcome) or a capability-query error returned a worker ERROR without
`compiler.not-started.sdn` or `capacity.settled`. The manager could not establish
terminal ownership, so a fresh manager treated an already rejected task as an
unknown live worker and refused recovery.

The existing memory-admission refusal writer is now a private helper shared
with these two capability refusals. It records the exact task digest, host and
reason, followed by `no-parent-owned` capacity settlement. The worker still
returns exit 2 and an empty-output ERROR. The manager's existing validation
requires both receipts and the matching ERROR result; no terminal validation
or V4 capability requirement changed. Calls occur strictly before executable
pinning or process start, and this portable worker never acquires a delegated
capacity parent. Errors after the capability gate retain their existing
ownership handling and never receive this no-child proof.

## Executed evidence

The regression invokes the production portable worker with staged, hashed
inputs and a monitor-policy task on native macOS. The actual Phase 1
interpreter capability query reports V4 unavailable; no provider is mocked.
The production transport then recovers the retained ERROR with a fresh
manager attempt. This is source-level admission/recovery evidence, not a
native compiler execution or containment qualification.

Retained Phase 1 producer generation:
`aa58a24ebe00248b428d4507e5cb0c58ec497c28ec8b2a3ed71ec65d697f756c-ecd1ed1cbf3f68a7abc6c2f852358542fae0b6e2e66c88e5abfcd5ea22cb3d2b`
under `/Users/ormastes/wt/release-bootstrap-integration-20261025/src/compiler_rust/target/bootstrap.generations/`.

Run each file independently:

```
SIMPLE_LIB=src <producer>/simple test test/01_unit/app/bootstrap_builder/worker_capability_refusal_spec.spl --mode=interpreter --assert-ran --no-cache --no-db --no-session-daemon --sequential
```

- Before the fix, the initial two regression cases failed: the refused worker
  was nonterminal, and a failed settlement write had no specific diagnostic.
  Log: `/tmp/buildrunner-capability-refusal-red.log` (0/2).
- Final regression: 3/3. Exact identity/host rejection proof and ERROR recover;
  a substituted host or successful result cannot settle; failed no-child or
  capacity persistence remains nonterminal; no reap marker is emitted.
  Log: `/tmp/buildrunner-capability-refusal-final-green.log`.
- Existing `memory_policy_spec.spl`: 6/6; `no_child_started_spec.spl`: 3/3.
  Logs: `/tmp/buildrunner-memory_policy-green.log` and
  `/tmp/buildrunner-no_child_started-green.log`.
- The working environment-facade guard and whitespace check passed, and the
  executable-spec count under `doc/06_spec` was zero.

No Phase 2 rebuild or binary deployment was performed. Full native compiler,
library and MCP gates remain unverified. A positive native Hello still needs
the complete Darwin V4 provider; this fix only makes its refusal recoverable.
