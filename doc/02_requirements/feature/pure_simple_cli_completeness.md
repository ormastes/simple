# Pure-Simple CLI completeness requirements

- REQ-001: A self-pinned CLI must not execute itself as a delegate.
- REQ-002: With no delegate, `-c` must stage and interpret a `main` function.
- REQ-003: The full CLI must link without unresolved `walk_dir` fallback.
- REQ-004: `test` must dispatch through the pure-Simple runner.
- REQ-005: Interpreter test children must report a summary and fail when an
  example is red or when no examples execute.
