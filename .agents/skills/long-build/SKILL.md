---
name: long-build
description: Coordinate long Simple builds and test matrices through finite dependency scheduling, resource monitoring, cache-preserving continuation and parallel failure repair.
---

# Long Build

Use the [shared collection policy](../../../doc/07_guide/tooling/bootstrap_failure_collection.md)
as the continuation contract.
Use its [cached object continuation workflow](../../../doc/07_guide/tooling/bootstrap_failure_collection.md#cached-object-continuation-and-early-linking)
when a failed aggregate build still has reusable successful files. Read only
the last log line, exit code and object size for successful compile observation;
inspect additional diagnostics only for failed runs.

1. Freeze the requested build/test inventory and dependencies. Record producer,
   source, runtime/tool identities, cache owners, outputs and current user worker
   preferences. Distinguish backend threads from memory-heavy frontend processes.
2. Run eligible independent rows in parallel within the selected resource
   policy. Monitor actual child progress, CPU, RSS, elapsed time and exit status;
   an idle parent waiting on a child is not proof of a stalled build.
3. Let independent jobs reach terminal results after sibling failures. Collect
   every failure and delegate distinct causes to parallel repair agents. Missing
   prerequisites block only their dependent rows.
4. For an explicit user-authorized time/memory/policy bypass, keep a separate
   monitored DIAGNOSTIC attempt with its disabled checks and retained failures.
   Do not silently reintroduce disabled enforcement through an outer wrapper.
5. On an actual restart, integrate latest requested release and reviewed
   applicable unmerged fixes into an isolated frozen source owner. Preserve
   compatible frontend/HIR/native caches and never share mutable caches between
   live writers or force identity stamps.
6. Advance a compiler lineage provisionally only after its real Hello compile
   and output execution pass. Continue full verification independently, restoring
   normal gates before formal promotion.
7. Finish the finite graph with truthful PASS/FAILED/BLOCKED/SKIPPED rows and
   actual test counts. Reuse green results for unchanged inputs; stop at
   convergence and never run an indefinite identical retry loop.
