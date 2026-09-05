# Cross-platform `sys_get_args` NFRs

- NFR-001: argument publication occurs once before user module execution.
- NFR-002: reads preserve order and empty arguments and never return nil for a
  valid array.
- NFR-003: invalid Windows UTF-16 is replaced with U+FFFD without panic.
- NFR-004: strict native linking rejects missing argument providers.
