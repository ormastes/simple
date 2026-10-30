# BuildRunner retention lifecycle with actual worker receipts

Status: authored manual outline, **NOT_RUN**. Source:
`test/02_integration/app/buildrunner/scv_retention_lifecycle_v2_spec.spl`.
This file is not generated execution evidence and does not claim runtime PASS.

Supply admitted `BUILDRUNNER_RETENTION_TEST_RUNNER`,
`BUILDRUNNER_RETENTION_TEST_WORKER`, `BUILDRUNNER_RETENTION_TEST_PROCESS`,
`BUILDRUNNER_RETENTION_TEST_MEMORY_PROVIDER=cgroup-v2`, and `SIMPLE_LIB=src`.
The process executable must be built from
`test/fixtures/buildrunner/scv_retention_process_v2.spl`. It writes known fixture
bytes, terminates itself through a real signal once, or waits for cancellation.
It is not a compiler and cannot qualify native product compilation. The actual
Linux worker alone authors process, capacity and tree-reap receipts. Missing
providers are explicitly pending in ordinary assurance and fail closed under
critical assurance.

The retry scenario stages an isolated Git checkout, producer bytes and exact
task context. It invokes the real native manager with `run`, expects the first
child to be signal-terminated, then expects a successful second attempt reusing
only its copied retry-cache marker. The declared output must equal the exact
fixture bytes. Both attempt roots must have worker-authored reap evidence.
Normal completion must leave only the durable session dependent pin and no
reader lease or capture reservation.

The scenario next verifies the retained source through the real `verify`
command. It removes the first attempt's actual reap file while keeping the
current journal terminal. Verification and retirement must refuse, retain the
reader protection newly acquired by verification, and avoid publishing a
retirement marker. Restoring the exact saved worker-authored bytes allows
verification to release active protection again.

The test then holds the actual shared store lock and invokes `retire`. The
command must write its durable retirement marker before its store transaction
fails with code 2. The durable pin must remain; verification must already refuse
the retired state. After releasing the lock, an exact retirement retry succeeds,
and a second retry after successful unpinning also succeeds with identical marker
bytes. Only then may own pins, leases and reservation all be absent. `run` must
continue refusing the retired state.

The cancellation scenario starts the real manager asynchronously, waits for the
fixture child's physical start marker, and writes the manager's cancellation
request. The manager must return 130 after the actual worker records tree reap.
Both pins and the reader lease remain. Retirement refuses with the cancel request
present and still refuses after its removal because the journal has not become
ordinary settled work. No retired marker or reader release is permitted.

Run SPipe docgen and manual maintenance only after general-runtime admission.
Inspect real assertion counts and provider provenance; pending coverage is not
execution success. Performance, all dependency graphs, source-compiler product
qualification and release readiness are outside this authored evidence.
