# Common primary input entrypoint refusal specs V2

Status: **AUTHORED SOURCE-ONLY NOT_RUN**. No test, build, native operation or
positive input fixture was executed. Production modules remain unchanged.

Production snapshot: `src/lib/nogc_async_mut/container/terminal_primary_input_v2.spl`.
SHA256: `1ad71363411bd0db70a3065b836dece0a3a0cf106c4fad22962077975f8b4534`.
Spec: `test/01_unit/lib/nogc_async_mut/container/terminal_primary_input_v2_spec.spl`.
No `terminal_session_v2_spec.spl` exists in the inspected unit directory.

| Exact authored test name | Intended semantics |
|---|---|
| rejects Legacy OutputFollow gate observation before native state access | Actual `container_primary_input_gate_v2` refuses the wrong owner with `container-primary-terminal-required`; pure Legacy projection and output identity remain available |
| rejects Legacy OutputFollow installation before unissued credentials can reach a provider | Actual install entrypoint refuses both ordinary unissued metadata and malformed metadata at the owner-kind boundary; no native installation or invented gate success is asserted |
| rejects Legacy OutputFollow revocation without inventing a successful no-op | Actual revoke entrypoint refuses the nonprimary owner; original Legacy transfer projection and identity remain intact |

The fixture follows the existing metadata-only convention in
`test/01_unit/os/apps/smux/runtime_terminal_ref_spec.spl`. It reuses
`container_primary_attach_fixture_v1` for pure launch metadata and computes the
profiled identity through the production helper. Its synthetic process reference
is never treated as an admitted or live native transfer. The public lease and
target values are explicitly unissued metadata, never opaque capabilities.

Source inspection bounds these authored failure paths: each entrypoint calls
`require_adoption_v2`; the common primary view rejects `Legacy.OutputFollow`
before reading any native input state or dispatching install/revoke. The
compatibility assertions use only Legacy projection and pure metadata identity
comparison. No frozen production module was modified to facilitate testing.

Actual native positive fixtures are unavailable. These cases do not cover an
adopted Linux primary's gate values, Linux Unknown normalization, Windows
binding/current/pending/Unknown normalization, raw nonce delivery to provider
validation, actual post-install observation, concurrent revocation, or native
revocation effects. They fabricate no Windows lease, primary adoption, native
receipt or passing gate. No branch-coverage, native Windows qualification or
production-readiness claim follows from this source-only file.
