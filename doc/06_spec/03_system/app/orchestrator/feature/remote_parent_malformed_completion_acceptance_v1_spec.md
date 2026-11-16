# Remote parent malformed completion acceptance V1

Status: AUTHORED_NOT_RUN. One registered modern SSpec scenario, five steps.
Requirement: AT-RUN-02, partial parent-admission integration only.

The scenario invokes the released parent decoder/session and real temporary
file, database and WAL APIs. Existing fixture signatures authenticate synthetic
remote observations. No remote producer, container, installed credential,
native tree-reap query or agent is run. This is not full RUN-01/RUN-02 acceptance.

| Step | Actual action and oracle |
|---|---|
| Open actual parent journals | Use the existing container-parent fixture/open helpers; retain the returned actual session before assertions and save exact operation/history. |
| Reject truncated wire before publication | Remove the final delimiter from the actual encoder result; require the production parent to return REMOTE_CONTAINER_BUNDLE_WIRE_INVALID, preserve empty task history and leave the expected accepted artifact absent. |
| Close/reopen and compare exact retained bindings/history/absence | Close both real journals positively before reopen; compare operation ID, whole envelope, envelope digest, state, outcome digest and exact empty history. Artifact remains absent. |
| Accept original fixture once | Feed the original complete wire through the same production parent; read exact binary artifact bytes from its returned output root, require one history row and reject replay without another row. |
| Close exact owners | Require actual positive task-journal and operation-journal close results. Teardown removes only the fixture-owned temporary root after confirmed cleanup. |

`acceptance_remote_parent_close_v1` keeps separate positive-close flags, full
returned Result values, a sticky first cleanup diagnostic and the actual session
carrier. Each journal close is attempted at most once per actual opening. The
independent second journal may close once in that same turn, even if the first
is uncertain. Every later cleanup call returns the original diagnostic without
another native close; later success cannot erase uncertainty. It never treats
stale/error as consumption. Attempt results reset only after prior complete
positive cleanup and a new confirmed opening.
An uncertain close or incomplete setup blocks reopen, later effects and root
removal. Published owners and the known test-root path remain recorded. The
released convenience open helper acquires the operation journal before later
fallible setup calls and does not return partial setup owners on error. A
setup-pending marker is an explicit blocker, not custody or cleanup proof for
an owner that helper never returned. This test does not qualify setup-fault
recovery; that requires a real partial-owner setup port or separately owned
fixture provisioning. The old
convenience release helper is not used after a partial close.

Prerequisites: admitted self-hosted SSpec runtime, existing released fixture and
remote-parent modules, private temporary filesystem/lock/database support and
the production pure Ed25519 implementation. Missing prerequisites fail rather
than skip. No production authority is manufactured by the new helper.

Dependency pin (git blob ids, identical at release 4934dd32445 and at
origin/release/1.0.0 9688ab99d83): `test/fixtures/buildrunner/remote_container_parent_v2.spl`
2d7d67e005, `src/app/buildrunner/remote_container_session_v2.spl` ca8d51668c,
`src/app/buildrunner/remote_container_bundle_codec_v2.spl` 3107f2aa1c. It does
not qualify the pending cycle7 assembly's modified journal implementation. No
tests, compiler, docgen, provider or native commands were executed: no `simple`
binary was available, so the scenario is NOT_RUN.

Remaining full-row gaps: verified remote selection/composition, genuine Host
completion production, live input/output identity checks, reset-failure evidence
and actual incomplete native/container cleanup fault execution. Those remain
separate blocked requirements and are not satisfied by this scenario.
