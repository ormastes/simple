# Partial host startup ownership

Status: **AUTHORED_UNRUN**. Source:
`test/01_unit/os/apps/smux/runtime_binding_startup_owner_spec.spl`.

Three pure consumer scenarios verify the actual policy-failure projection used
after opening a host root. Retained, unknown and consumed-error outcomes keep
the canonical cleanup carrier, lock generation and release state. Only the
exact released/closed/no-error/no-cleanup combination is a clean rejection.
Stale or consumed-error metadata cannot become successful cleanup.

The test tokens are pure metadata and never enter native IO. Native journal
failure injection and the real configured server remain separate required
checks; these scenarios do not prove that a host writer was closed.
