# Architecture: Pure Simple SSH and HTTPS Servers

## Scope

Selected feature option: Boundary-First Release Slice.

The architecture separates protocol state machines from host access:

- Pure Simple protocol layer: SSH, TLS, and HTTP parsing/framing/state.
- Host access adapter layer: socket accept/read/write, time, entropy,
  filesystem/certificate/key access, and process execution.
- Compatibility layer: existing native SSH/TLS SFFI wrappers remain available
  for alpha/beta comparison and legacy callers, but are not release-mode
  protocol paths.

## Layering

### Protocol Layer

SSH protocol modules remain under `src/os/apps/sshd/` and own version exchange,
KEX, authentication, encrypted packet handling, channels, shell, and exec.

HTTPS protocol composition uses existing HTTP and TLS Simple modules:

- `src/lib/nogc_async_mut/io/tls*.spl` for TLS record/handshake/application data.
- `src/lib/*/net/http.spl` and HTTP server modules for HTTP request/response
  behavior.

### Host Access Adapter Layer

Adapters expose capability records and mode decisions. They must not parse or
implement SSH/TLS/HTTP protocol semantics. They may provide:

- accepted byte stream handles
- read/write/close
- current time and timeouts
- entropy
- certificate/key file access
- process execution for SSH command handling

Hosted Linux and SimpleOS use different adapter implementations behind the same
protocol-facing policy.

### Mode Layer

The lane uses explicit mode names:

- `alpha`: run Simple protocol and compatibility/native path, fail closed on
  mismatch where a comparison path exists.
- `beta`: run Simple protocol and compatibility/native path, record a critical
  mismatch report while keeping the primary result.
- `release`: run only the Simple protocol path. This is production mode.

## Release Rule

Release-mode entrypoints must call Simple protocol modules. Native SFFI wrappers
that implement complete SSH/TLS protocol behavior are compatibility paths and
must not be selected silently by production wrappers.

## Verification Strategy

- Unit tests prove mode selection and host-access capability policy.
- Integration/system specs prove release-mode routing for SSH and HTTPS.
- Hosted Linux smoke proves each release-mode server path at least once.
- SimpleOS live gate evidence is required before final release; if QEMU blocks
  it, the blocker must be concrete and linked.

## Open Risk

The existing TLS server scope appears TLS 1.2-oriented. This architecture does
not claim full TLS 1.3 support until a later selected option adds conformance
and security coverage.
