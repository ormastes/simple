# Native-build environment timeout system test plan

- REQ-NBET-001: scoped per-file environment timeout resolves in Rust driver and native-all.
- REQ-NBET-002: worker timeout is resolved only from the worker scoped key.
- REQ-NBET-003: CLI source overrides environment source.
- REQ-NBET-004: invalid and zero values fail before build spawn.
- REQ-NBET-005: normalized and explicit scoped keys are deterministic.
- REQ-NBET-006: verbose receipt contains value, source, and key.
