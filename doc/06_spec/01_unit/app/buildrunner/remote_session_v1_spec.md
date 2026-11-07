# Remote parent session operation collection gate V1

Status: **AWAITING_VERIFICATION** — source-authored manual. No compiler, seed,
test runner, journal operation, or remote execution was run for these specs.
This records intended assertions and makes no execution or coverage claim.

Source: `test/01_unit/app/buildrunner/remote_session_v1_spec.spl`.
Implementation: `src/app/buildrunner/remote_session_v1.spl`,
`remote_operation_collectable_v1`.

The fixture encodes the actual request supplied by
`test.fixtures.buildrunner.remote_authority_v1`, then creates the retained
state with `distributed_operation_initial_v2`. Executing, outcome-unknown,
cancelled, completed, and failed states use
`distributed_operation_transition_v2`. Direct state mutation is confined to
the negative binding-corruption cases.

| Scenario | Intended assertion |
| --- | --- |
| Executing | Exact operation id, encoded envelope, and retained SHA-256 digest accept. |
| Outcome unknown | The exact binding accepts reconciliation after transitioning from executing. |
| Admitted | Collection before the execution transition rejects with `REMOTE_EXECUTION_NOT_STARTED`. |
| Cancelled | Cancellation from executing and outcome-unknown rejects with `REMOTE_EXECUTION_CANCELLED`. |
| Completed or failed | Both terminal states from both collectable predecessors reject with `REMOTE_COMPLETION_REPLAY`. |
| Different operation id | Changing either caller id or retained id independently rejects with `REMOTE_OPERATION_BINDING_DIFFERS`. |
| Different caller envelope | A separately valid encoded request with changed payload digest rejects against the retained request. |
| Changed retained envelope | Matching mutated caller and retained envelope text reject when their original retained hash remains unchanged. |
| Changed retained hash | Matching envelope and id text reject with a substituted retained digest. |

These are pure function specifications. They do not verify database or operation
WAL persistence, cancellation delivery to a real process tree, two-journal crash
recovery, staging directory cleanup, lock lifecycle, signing, or publication.
Those integration behaviors require separately qualified runtime evidence.
