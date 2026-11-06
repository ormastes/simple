# Node attributes: lifecycle integration progress

Target branch: `release/1.0.0`. Date: 2026-11-06.
Architecture/design landed in #7228. Status: implementation in progress;
execution qualification pending. This is not full node-attribute completion.

## Canonical ownership and review resolution

PR #7241 was rebased onto release commit `d3b2459be58` after the owner review
identified the schema resolver already landed in #7220. There is one resolver:
`compiler.common.data.data_schema_resolver.data_schema_resolve_v1`, producing
`DataSchemaSurfaceV1` with `data_schema_digest_v1`.

The duplicate NodeAttribute schema contracts, resolver, ordering, dependency
validation and semantic encoding were removed from this change. The experimental
compiler contexts, property bindings and annotation adapter that depended on
those types were also removed. Their authored test counts are not qualification
of the canonical implementation and are no longer reported as current coverage.
Source/SDN, visibility/effects, computed properties, independent contexts and
explicit off-mode behavior remain full-feature requirements. Extend the canonical
owners for these features rather than restoring a parallel schema stack.

`src/compiler/00.common/data/node_lifecycle_contracts.spl` retains whole-node
Pending/Ready/Discarded facts, the initialization bitmap, retaining finish failure,
duplicate-init checks, explicit discard recording and unresolved-scope diagnostics.
It now consumes `DataSchemaSurfaceV1`, validates its digest and canonical one-based
attribute IDs, and binds facts to that digest. It moved out of library/common
because importing the compiler-owned schema there would invert the dependency.

The canonical V1 schema describes stored fields and infers views from fields.
The lifecycle adapter therefore refuses an unknown/fieldless view rather than
inventing a view declaration. Computed/forwarded readiness and explicit empty
views require extension of that owner before admission. All applicable stored
slots, including optional absence/default values, require actual initializer
commits. No implicit zero or inferred executed default is introduced.

These are semantic facts, not user-owned payloads or mintable runtime authority.
They do not allocate, clean up, publish or retire nodes, execute defaults, enforce
language must-resolve rules, or replace topology/borrow checks. Digest checking
is on this cold fact path, not on ready-node reads.

## Evidence

`test/01_unit/compiler/data/node_lifecycle_contracts_spec.spl` authors eleven cases
against the canonical resolver: retaining failure, default bookkeeping, duplicate
initialization, discard, digest mismatch, canonical ID bounds, stale surfaces and
unsupported versions, refusal of an unrepresented empty view, cross-view
applicability, explicit optional-absence commits and malformed IDs/bitmaps. These have
not executed; no passing count or coverage percentage is claimed.

The separate canonical Windows LLVM bootstrap remains pinned to release commit
`6e03930143983a5c9861321f67aff300b07f16ed`. It uses
`bootstrap-windows.sh --msvc --strategy=normal --full-bootstrap --stop-after-stage2
--backend=llvm --jobs=1`. Attempt 4 passed materialization verification and native
C admission and entered seed compilation; the supervised Cargo process spawned
successive rustc processes. This document does not prove current process liveness
or successful bootstrap. Logs remain in the frozen worktree at
`build/node-attributes-qualification/bootstrap-attempt4.log`.

Earlier attempts established environment failures: MSYS Python was incompatible
with the native supervisor; a restricted PATH lacked PowerShell; Git-for-Windows
failed receipt validation before compilation. No receipt gate was bypassed.
Installed Rust seed executables were not used for feature tests. #7220's reported
seed test evidence is not pure-Simple qualification of this lifecycle adapter.

## Remaining landing and feature gates

Execute the lifecycle spec with an admitted pure-Simple runtime, assess failure
coverage, and complete applicable compiler/lib/MCP checks before marking this
change qualified. Review the exact pushed diff and comments before landing.
The broader requirement matrix remains in `doc/03_plan/sys_test/node_attributes.md`:
source/SDN declaration binding, generated places, real builders and cleanup,
lifetimes/topology, storage layouts, engine parity, AOP, tracing, cache/LSP and
Simple/BuildRunner adoption remain required. W2c should build on this lifecycle
contract and the canonical resolver, not a new resolver.
