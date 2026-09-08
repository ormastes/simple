# Stage-2 Rust transient promotion rejects positional hello world

**Date:** 2026-09-09
**Status:** Repair implemented; focused Rust and native-all-provider regression
tests pass. Fresh Stage-2 admission remains required.

## Observed boundary

After the Stage-2 runtime ABI/link gaps were fixed, the compiler linked and
entered the four-fixture frontend admission. The first three fixtures passed.
The positional hello-world fixture failed during MIR lowering:

```text
[ERROR] MIR error: MIR lowering transient scope failed for
scripts.check.cert.redeploy_gate.fixtures.hello_world:
MIR lowering owner promotion failed for
scripts/check/cert/redeploy_gate/fixtures/hello_world.spl
```

The core-C `rt_transient_heap_thread_affinity_selfcheck` passes after unifying
its raw allocation registry. Stage 2, however, links `libsimple_native_all.a`
and therefore uses the Rust implementation of `rt_transient_heap_promote`.
This is a separate owner-graph classification/promotion defect in the Rust
runtime path, not a missing symbol or package-index initialization failure.

## Evidence

```text
/tmp/simple-bootstrap-kv-final-20260909/logs/aarch64-unknown-linux-gnu/stage2-native-build.log
/tmp/simple-bootstrap-kv-final-20260909/stage3/aarch64-unknown-linux-gnu/stage2-sanity.env.frontend-driver.log
```

## Required acceptance

- Reproduce the failing positional fixture against the freshly linked Stage-2
  candidate with bounded admission infrastructure.
- Identify the exact Rust heap node/value rejected during promotion; do not
  weaken the fail-closed classifier.
- Add a focused Rust regression test for the rejected graph shape.
- Pass the four-fixture candidate frontend admission in bootstrap modes 0 and 1.
- Pass one fresh-root Stage-2 bootstrap admission and preserve its receipts.

The session reached the mandatory three-cycle bootstrap cap after producing
this evidence. Further repair and verification must start in a fresh session.

## Repair

`runtime_memory.c` now lets the transient graph walker recognize a root only
when it is present in either the transient raw-owner table or the existing
live native-struct allocation registry. A persistent native-struct root is
already outside the transient reclaim set, so its promotion is a validated
no-op, while its exact registered allocation size bounds traversal of fields
that can lead to transient children. Arbitrary and stale pointers remain
rejected.

The Rust runtime regression
`persistent_native_struct_root_promotes_transient_children` constructs the
same ownership shape: a native struct allocated before the scope, containing
a string allocated inside the scope. It passes both the ordinary runtime and
the production `native-all-provider` composition and proves that the child
survives scope end.
