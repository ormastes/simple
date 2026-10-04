# Configured mapped-provider dispatch

Date: 2026-10-04. Release base `b0f0cf98787`. ITEM4-REQ-010 / linker G5.

The real native-build integration point is llvm_native_link_orchestrator.spl
after runtime/entry objects and explicit link options have been assembled.
Routing earlier, or using the legacy request adapter, loses libraries, paths,
runtime selection, PIE/debug/strip/size/verbosity, duplicate/fallback policy,
retained symbols, extra flags and target/ABI. Shared-image emission uses a
separate route and must not accidentally enter executable dispatch.

`simple-link-job-v2` transports all 15 NativeLinkConfig fields in addition to
the validated V1 request/policy/input/output envelope. V1 remains available.
The provider dispatches V2 directly to `link_request_to_native_with_config`;
it must never retry V2 as V1 or replace caller configuration with defaults.
The existing command ABI identifies the V1 command interface, not a claim that
every old artifact accepts the new argv tag. An old artifact must reject the
unknown V2 tag explicitly. No configuration/manifest authority is inferred from
the unchanged policy digest or generic command ABI.

Lifecycle configured dispatch preserves generation pins and running guards.
An optional configured callback explicitly distinguishes static providers that
can accept the full context from legacy callbacks. Missing configured callbacks
reject before invocation. The mapped owner is extracted to a mutable local and
written back before propagating errors. Static configured recovery bypasses
publication/session capacity and uses the independently retained operation.

Tests cover every field, malformed transport and resource bounds, explicit
legacy-callback rejection, and successful links through actual mapped packs:
first/repeated output, pinned replacement, unload after close, failed replacement
preserving active service, and recovery under exhausted capacity. Independent
ELF fields and process exit status provide output oracles. Tests require an
admitted native Linux runtime/provider and hosted tool/runtime dependencies.

## Open production authority

No linker-specific trusted manifest loader exists at this base. Generic artifact
eligibility code consumes externally authoritative trust receipts; it is not a
signature verifier. The descriptor sealer likewise does not authenticate an
artifact. Production CLI selection must retain an existing opaque admitted
activation or real authorized manifest owner; hashing an arbitrary selected
file and accepting that same digest is not authorization. The future closed
declaration issuer cannot supply this authority.

CLI selection, actual required-facet operation binding/seal, dependency closure,
immutable mapping, signatures, shutdown ownership, resource enforcement and
runtime qualification remain open. These source changes do not close the six
original PACK-POS production-composition obligations or grant Phase 4 PASS.
