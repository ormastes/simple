# Common primary write and observation refusal specs V2

Status: **AUTHORED SOURCE-ONLY NOT_RUN**. No tests, builds or native operations
were executed. Only this new spec and manual were authored by this worker.

Production snapshot: `src/lib/nogc_async_mut/container/terminal_primary_write_v2.spl`.
SHA256: `8a84cd5ae16aad9d771b2a6aaa23b32f8f4f8bca5885fc0f6fa6e2ea7bffb97a`.
Spec: `test/01_unit/lib/nogc_async_mut/container/terminal_primary_write_v2_spec.spl`.

| Exact authored test name | Intended semantics |
|---|---|
| rejects Legacy OutputFollow write before any provider invocation | Actual write entrypoint returns `container-primary-terminal-required`, preserving the Legacy output transfer projection and identity |
| rejects Legacy OutputFollow observation instead of manufacturing absent or completed history | Actual observer returns an owner-kind error, rather than a fabricated completion or `None`; Legacy metadata remains intact |
| keeps wrong-owner refusal ahead of malformed write and observation request bounds | Both actual entrypoints reject the wrong owner before malformed public request fields reach a native provider; Legacy identity is unchanged |

The local fixture follows the existing pure metadata convention in
`runtime_terminal_ref_spec.spl` and reuses the public pure primary plan fixture.
Synthetic transfer metadata is never submitted to native validation, IO or
cleanup. Public request, target and lease metadata are explicitly unissued and
convey no actual grant, adoption or native ownership. The suite does not import
another entire spec or register its native scenarios.

Source inspection shows both entrypoints require an adopted primary view before
request bounds and provider dispatch. `Legacy.OutputFollow` fails that view
check. Legacy projection and identity assertions use pure metadata comparison;
their success does not establish a live provider stream.

Actual adopted native positive fixtures are unavailable. These authored cases
do not exercise Queued/Completed/Unknown receipts, exact Windows full-tuple
observation, accepted-prefix accounting, expiration/revocation observation,
nonce delivery, mismatched retained history, or native write effects. The
current Legacy Unknown contract preserves its actual `accepted_bytes = -1`
sentinel; this native case also remains untested. No positive receipt, opaque
Windows owner or adoption is fabricated to fill that coverage gap.

A returned error after actual provider invocation cannot prove no IO occurred;
the reserved attempt must remain Unknown until its exact native observation.
The pure wrong-owner cases here stop earlier and claim no native qualification
or production-readiness result. Source inspection found the imports and return
types consistent with the inspected production APIs; compilation was NOT_RUN.
