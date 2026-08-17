# CompilerDriverV1 bootstrap activation is blocked on a callable provider loader

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Impact

`src/compiler/80.driver/driver_provider_contract_v1.spl` and
`driver_provider_in_process_v1.spl` now define and implement the first coarse,
opaque numeric session/request/result boundary. The adapter keeps
`CompileOptions`, `CompilerDriver`, diagnostics, AST, HIR, and MIR private.

The concrete import in `src/app/cli/bootstrap_main.spl:11` cannot yet be
removed safely. That entry calls the concrete driver at
`src/app/cli/bootstrap_main.spl:330` and
`src/app/cli/bootstrap_main.spl:441`. Its existing comment records that the
previous lazy-library attempt linked undefined driver symbols because no
dynamic compiler artifact existed.

Replacing the import now would either restore that undefined-symbol failure or
invent a fallback that silently claims dynamic activation while still using
the statically linked driver. Both violate fail-closed provider admission.

## Unblock condition

The provider-loader lane must supply all of the following:

1. an independently built compiler-provider artifact exporting a
   process-callable `simple_provider_query_v1` entry;
2. native/SMF loader admission proving artifact digest, ABI/target,
   descriptor prefix, interface major/minor, and process-callable address;
3. a bootstrap-safe client for the numeric CompilerDriverV1 operations;
4. focused link/run evidence that `bootstrap_main.spl` has no concrete driver
   import or undefined driver symbols; and
5. fail-closed evidence for missing, non-callable, incompatible, and malformed
   providers without Rust-seed or static-driver fallback.

Current partial support: `src/os/smf/provider_loader.spl` proves SHA-256
artifact identity, capability/ABI/interface policy, symbol resolution, and
process-callability; `provider_generation.spl` retains pinned in-process
generations. No compiler-provider shared artifact, raw query-call bridge,
signature/target proof, or loader-handle/generation lifetime coupling exists,
so the concrete bootstrap import remains required.

Owner: provider loader / bootstrap-core integration lane.

Bootstrap reason for the current provider-boundary implementation: `none`.
Only the new provider modules and focused tests are expected to rebuild.
