# Linux adapter through Simple Container API V2

Source: `test/01_unit/lib/nogc_async_mut/container/providers/linux/simple_container_adapter_v2_spec.spl`.

Status: **AUTHORED / UNEXECUTED / AWAITING_VERIFICATION**. This is a source
manual, not runtime-generated evidence or a passing test report.

1. Projects actual canonical resources and retains the full common owner scope.
2. Refuses noncanonical bytes digest tampering and mismatched request identities before native effects.
3. Rejects every cross-scope plan field through the common owner before leaf dispatch.
4. Routes prepare create start reads stop and destroy with signed duration and opaque scope fence.
5. Rejects launch expiry at the final leaf boundary without consuming a successful create fixture.
6. Refuses unknown actions and launch actions on the read-only API without effects.
7. Refuses unsupported leaf effects and projects workspace intent rather than hiding it.
8. Recovers only an exact retained intent through the common API and preserves its scoped owner.
9. Rejects a fixture provider with a different opaque fence or provider generation.
10. Dispatches a native stop before generic nonforce destroy rather than relying on terminal cache.
11. Queries wait afresh after recovered exit and separates CLI status from workload exit.
12. Returns an independent exact-query absence receipt without mutating retained lifecycle state.
13. Never turns a destroyed tombstone into absence proof without consuming a dedicated query.
14. Refuses present native objects and engine errors as absence evidence.
15. Rejects unsafe partial foreign identifiers and digest tampering before an absence query.

The common owner wraps an explicitly scripted real Linux adapter. Tests pass
returned owners through the actual common project/apply/read/recover/intent and
absence dispatch, using exact typed native command fixtures. Synthetic host and
engine observations never certify production native identity or Podman.

A retained destroyed tombstone cannot replace a dedicated absence query. Present
objects, query errors, unsafe/foreign IDs, and digest mismatch return no receipt.
Fresh wait preserves raw output and distinguishes CLI exit from workload exit;
a destroyed cache cannot manufacture retained wait evidence. Launch expiry does
not stop running work or prevent retained authorized cleanup.

See `doc/05_design/linux_simple_container_adapter_v2.md` for ABI provenance,
scope/continuity rules, trusted deadline boundary, and remaining verification.

Execution-options source update (UNEXECUTED): Podman create vectors include
`--http-proxy=false`; typed environment/cwd are admitted. Managed stdin requests
now project successfully without starting a process. Actual primary attach uses
a distinct plan, fresh configuration observation and controlled native session;
see `doc/05_design/podman_primary_attach_v1.md`. Its scenarios remain NOT_RUN.
