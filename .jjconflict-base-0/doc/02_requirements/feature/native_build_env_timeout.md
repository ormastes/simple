# Native-build environment timeout requirements

- REQ-NBET-001: Native-build shall resolve `SIMPLE_NATIVE_BUILD_TIMEOUT_SECONDS` as its per-file timeout when no CLI timeout is supplied.
- REQ-NBET-002: The interpreted native-build launcher shall resolve `SIMPLE_NATIVE_BUILD_WORKER_TIMEOUT_SECONDS` independently of the per-file timeout.
- REQ-NBET-003: CLI timeout values shall take precedence over the matching scoped environment value.
- REQ-NBET-004: Invalid or non-positive scoped timeout values shall fail with a diagnostic naming only the scoped key.
- REQ-NBET-005: Shared argument APIs shall derive safe scoped names from executable/module and option names, and support an explicit owner key for unit-qualified options.
- REQ-NBET-006: Verbose native-build output shall record effective timeout and its source.
