# PostgreSQL mimic server requirements

- REQ-PGM-001: Implement PostgreSQL-like startup sessions in Simple.
- REQ-PGM-002: Execute simple queries through `PureDatabase` without SFFI.
- REQ-PGM-003: Return rows, command tags, SQLSTATE errors, and transaction status.
- REQ-PGM-004: Isolate terminated or unknown sessions.
- REQ-PGM-005: Default production execution to cached SMF/LSM or native artifacts.
- REQ-PGM-006: Treat direct interpreter execution as explicit development fallback.
- REQ-PGM-007: State compatibility boundaries truthfully; mimic is not full PostgreSQL parity.
