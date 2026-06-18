# Feature Requirements: Pure Simple SSH and HTTPS Servers

## Selected Option

Feature Option A: Boundary-First Release Slice.

## Requirements

- REQ-001: The release-mode SSH server entrypoint must route SSH protocol behavior through Simple modules, including version exchange, KEX, authentication, encrypted packet handling, channel open, and command execution.
- REQ-002: The release-mode HTTPS server entrypoint must route HTTP request parsing/routing and TLS record/handshake/application-data handling through Simple modules for the supported initial TLS/HTTP scope.
- REQ-003: Hosted Linux and SimpleOS must share the same SSH and HTTPS protocol modules and differ only through host-access adapters for OS-provided effects.
- REQ-004: Runtime/SFFI use is allowed only for OS access boundaries such as socket accept/read/write, time, entropy, filesystem/certificate/key access, and process execution.
- REQ-005: Existing native SSH/TLS SFFI protocol wrappers may remain as compatibility or alpha/beta comparison surfaces, but release-mode production wrappers must not silently bypass the Simple protocol stack.
- REQ-006: Public SFFI and runtime guidance must distinguish protocol logic from host-access adapters.
- REQ-007: The implementation must expose explicit `alpha`, `beta`, and `release` mode naming for this lane; `release` is the normal single-path production mode.

## Initial Scope Limits

- HTTPS may use the repository's current TLS 1.2 server capability and supported cipher-suite envelope; full TLS 1.3 is not part of this selected option.
- Broad SSH algorithm expansion is not part of this selected option.
- Native/SFFI protocol wrappers are not removed until release-mode Simple protocol coverage is verified.
