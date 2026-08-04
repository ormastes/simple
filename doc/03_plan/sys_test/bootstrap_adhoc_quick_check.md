# Bootstrap ad-hoc quick check test plan

1. Unit-test path classification, lane widening, unsafe escalation, exact
   markers, repeatable changed paths, and invalid arguments.
2. Build the detached-worktree tool with the verified Stage3 producer.
3. Run the built-in selftest.
4. Run a frontend positive capsule and a deliberately invalid negative capsule.
5. Confirm the receipt is content-addressed, local-only, and explicitly
   non-release.
6. Confirm a loader change exits with full-bootstrap-required status.
