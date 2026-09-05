# Scheduler Pre-Exit Preparation V1 Test Plan

- Prove persistence must become terminal before namespace binding.
- Prove namespace commits before launch-grant completion through the composed
  server cleanup receipt.
- Prove task/lifecycle/transaction duplicates are rejected while live.
- Pure coverage proves retry advances attempt identity exactly without wrap.
- Static coverage proves persistence calls precede namespace/grant calls and
  `Completed` is non-authorizing while `Consumed` is terminal-authorizing and
  retained pending a future scheduler publication/reap acknowledgment.
- Future fault-injection integration coverage must prove copied/conflicting
  command replay, stale handles, partial provider commits, cancellation
  quiescence, indeterminate retention, the 64-slot bound, generation retirement,
  and provider-consumption failure between the two owners.
- Production acceptance remains blocked until scheduler task-state wiring,
  fault seams, and provider execution exist; no `Zombie` claim is made by these
  unit contracts.
