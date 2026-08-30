<!-- codex-design -->
# System Test Plan — Aspect Registry Transaction

Executable target:
`test/03_system/compiler/aspect_dynload/registry_transaction_spec.spl`

Generated manual target:
`doc/06_spec/03_system/compiler/aspect_dynload/registry_transaction_spec.md`

Use the ten frozen steps and helper names from the detail design. Scenarios:

1. `REQ-REG-001`: cold coherent activation and ACTIVE-last publication;
2. `REQ-REG-002`: resident snapshot lease plus valid generation pin;
3. `REQ-REG-003`: real concurrent single-flight with stable shared success and
   a bounded deadlock timeout oracle;
4. `REQ-REG-004`: stable retryable failure followed only by explicit retry;
5. `REQ-REG-005`: failure injection after open/map/relocate/symbol/witness/
   sidecar/finalize with rollback;
6. `REQ-REG-006`: cycle A -> B -> A with complete stack unwind;
7. `REQ-REG-007`: quiesce, surviving old pin, rejection of new pin, double-unpin
   rejection, and final-unpin-driven retirement;
8. `REQ-REG-008`: partial unmap poisoning, explicit retry, and reload refusal;
9. `REQ-REG-009`: path replacement after open with coherent lazy payload;
10. `REQ-REG-010`: mutation after open cannot alter owned bytes, while mutation
    during capture fails the expected extent digest;
11. `REQ-REG-011`: bounded cache eviction preserves pinned snapshots and old
    snapshot reclamation waits for lease release;
12. `REQ-REG-012`: owner cancellation stores one retryable result; waiter
    cancellation detaches without cancelling the owner;
13. `REQ-REG-013`: startup eager-root single publication and lazy-root zero-I/O.

Every scenario asserts concrete counters, states, generations, identities, and
resource manifests with built-in matchers. Fail-fast helpers remain red until
real production evidence exists. Mutation controls cover early Active publish,
implicit retry, path reopen, missing section-class retirement, and stale-token
acceptance. Required fail-fast mapping:
`check_real_parallel_single_flight` -> REQ-REG-003;
`check_active_last_observation` -> REQ-REG-001;
`check_no_reopen_toctou` -> REQ-REG-009/010;
`check_complete_native_retirement` -> REQ-REG-007/008.
Additional negative controls cover snapshot reclamation, double unpin,
final-unpin retirement, owner/waiter cancellation, timeout/deadlock, and
in-place file mutation. Run each criterion once after the last change.
