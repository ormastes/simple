# HIR shard ABI receipt rejects its existing scratch owner

Status: source repair prepared; native correctness and paired resource evidence pending.

Base: local `release_temp` at `cc05d7f451467657a6cf5fc464dfd09d8239ef9f`.
Owner: `C:/dev/simple-release-temp-memory-perf-20261005`, branch
`work/release-temp-memory-perf-20261005`. Original worktrees and caches are preserved.

## Reproduction and cause

`CompilerDriver.lower_streaming_hir_shard_transaction_v1` begins a transient
scope and calls `driver_log_typed_hir_abi_interface_v1` before pausing it.
The logger calls `driver_hir_abi_interface_digest_v1`, whose own scope acquisition
must reject nesting. Consequently both a decoded HIR cache hit and newly lowered
HIR emit `abi-interface-unavailable` with `ABI interface scratch scope unavailable`
instead of their typed HIR digest. The existing nested-owner unit regression
explicitly requires this refusal; changing acquisition to succeed would violate
the scratch ownership contract.

## Repair

The shard invokes an explicit in-owned-scope digest function. It retains only
the pair `(module_name, Result<digest, diagnostic>)` while its scope is paused.
The existing owner ends the scope, then logs that retained receipt. Encoder
scratch and the HIR graph remain reclaimable. Promotion failure follows the
existing fatal ownership path. The ordinary standalone digest still acquires
and closes its own scope and still rejects a nested caller.

The logger still reports encoder errors as unavailable. Cache headers, keys,
dependency identities, atomic publication, and admission rules are unchanged.
The fixture exercises both success and dynamically allocated error results,
owner closure, subsequent independent ownership, and retained-allocation growth.

## Verification and resource evidence

- Source inspection proves the old nested call; native reproduction is pending.
- Whitespace and static shard receipt-order checks passed. The working-tree
  direct-env-runtime guard passed; `doc/06_spec` contains zero executable specs.
- `test/01_unit/compiler/driver/hir_abi_interface_scratch_spec.spl` adds native
  borrowed-owner correctness and reclamation tests. Its paired eight-iteration
  row reports elapsed microseconds and retained heap registry entries for
  borrowed versus unscoped encoding. Registry entries are not RSS.
- Native tests have NOT run. There is no measured performance improvement,
  memory improvement, release admission, or production readiness claim.
- No compatible idle native cache for the new entry has been proven. Existing
  native validation recipes are pinned to source `703b591a` and producer
  `cfa73ac440cd4fc1d0671610d3d8493b267aab4ecfa46612db2e95b5d99f0bdd`;
  running them cannot establish the changed driver's shard receipt behavior.

For the next authenticated source freeze, run the native scratch spec and the
existing cold/warm HIR-shard fixture using a producer rebuilt with this repair.
Require an actual `[abi-interface]` receipt for each valid shard module and no
scratch-unavailable diagnostic. Retain compiler/fixture identities, cache hit
counts, module results, elapsed p50/p95 and peak/steady RSS for equal baseline
and candidate workloads. A repaired receipt does more real work than the old
rejected receipt, so compare resource cost honestly rather than calling it a
speedup. Keep cold and warm build rows separate. The user-authorized diagnostic
mode monitors time/RSS without enforcing limits; cleanup and identity checks
remain mandatory, and diagnostic completion is not RC admission.
