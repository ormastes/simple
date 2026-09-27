<!-- codex-design: Astra, 2026-09-27 -->
# Frontend Advisory Execution Authority V1

**Status: proposed authority milestone; implementation and qualification pending.**

This companion extends [the parent detail design](environment_optimized_dynamic_libraries.md)
and its Stage 3 frontend insertion. It does not change defaults, declare parser
replacement, or qualify native SIMD performance. Selected requirements remain
REQ-003/004/005/006/008/009/012/013/014 and NFR-001–010 in the existing
environment-optimized-dynamic-libraries requirements. The parent design is
being edited by other lanes; this document is additive.

## Current production boundary

`driver_source_pipeline_parsing.spl:parse_full_frontend_selected_v1` calls
`frontend.spl:parse_full_frontend_with_advisory_policy_v1`. The shared frontend
dispatches after conditional/domain transforms and before parse-cache lookup.
`frontend_advisory_preprocess_dispatch_checked_scoped_v1` currently always
constructs reference/unavailable evidence. Numeric startup coordinates only
correlate a lifetime; they cannot select executable code.

`environment_variant_startup_binding_v1.spl` retains sealed activation authority
but its private provider-adapter registry is empty. Its factory registration
has no production candidate installer. The older
`frontend_lexical_advisory_binding_v1.spl` references removed bind/reset APIs;
restoring them would reopen arbitrary callback admission.

The existing native route is real: `frontend_lexical_advisory_adapter_run_v1`
calls `parser_structural_package_lexical_batch_v1`, guarded lexical masks, and
the loader-private `rt_parser_lexical_mask_call_u8x32` wrapper. Mapping, source,
generation and capability owners authorize those calls; masks are compared to
the scalar oracle. Copyable adapter results and correctly hashed receipts are
not execution authority. Existing reference-only tests do not prove this route
is reachable from the compiler frontend.

## Canonical interface and ownership

Freeze these proposed names for the implementation handoff:

- `FrontendAdvisoryExecutionOwnerV1`
- `FrontendAdvisoryExecutionTokenV1`
- `frontend_advisory_execution_issue_v1`
- `frontend_advisory_execution_consume_v1`

The owner is proposed in
`src/compiler/99.loader/frontend_advisory_execution_owner_v1.spl`. Its mutable
records and issuing operations stay private to the loader composition boundary.
The token is opaque owner/epoch/operation coordinates, never a function address,
caller-built receipt, or replacement for a native mapping capability. Copying
the token conveys no additional use. Public constructors or field mutation must
not recreate a live owner, issue a token, or install executable callbacks.

Threat model includes untrusted constructed token values, guessed sequential
coordinates, cross-owner/session substitution and replay of a copied valid
token. Coordinates alone are insufficient: each live table row also requires
an unguessable nonce minted by the admitted runtime capability owner and bound
to that exact owner/epoch/request/startup session/generation. The private row,
not a public checksum, is authoritative. If that native capability source is
unavailable, issuance remains unavailable; do not substitute a counter or hash
of public fields. Copying a legitimately held token shares its single permitted
consumption. Recovery invalidates all old epochs; no token survives owner
restart. Failed guesses cannot consume or mutate the legitimate row.

Layer 10 owns a lower-layer typed request/result port. The composition root may
install only the fixed loader adapter using an owner-issued issuer capability;
there is no public callback registry. Implementation review must establish the
language-enforced private issuer boundary before enabling dispatch. If that
boundary cannot be enforced, keep dispatch unavailable and report the blocker.
Layer 10 must not import layer 99 or resolve raw addresses itself.

Metadata transitions are serialized in the canonical owner. Reject reentrant
operations; do not hold the owner lock across mapping, native calls, hashing or
cleanup. Reserve a bounded record before leaving serialization and validate its
epoch when committing results. Never copy mutable owner state to grant authority.

## Admission and per-source lifecycle

1. The trusted composition root binds a live sealed frontend activation to an
   existing authenticated lexical package activation. Join exact provider,
   variant, artifact, ABI/mask/tail identities, publication generation,
   environment identity/generation and policy. A generic frontend facet handle
   alone cannot manufacture a lexical package. Revalidate the join on each use.
2. Frontend preprocessing produces one immutable transformed-source request.
   Independently compute its byte length and digest, dialect/grammar/actions/
   semantic identities, lexical input state, policy and startup owner/session/
   generation. Do not derive expected values from returned provider evidence.
3. `frontend_advisory_execution_issue_v1` takes the retained owner and this
   bounded request, not a session, callable, execution count or receipt supplied
   by the caller. Acquire the sealed build-use and create a fresh package source
   session via `parser_structural_package_v2_source_session_v1` over those bytes.
   Reset/append callers receive separate requests for their actual transformed
   snapshot; an old session cannot be reused for changed input.
4. Invoke the existing lexical adapter on complete 32-byte blocks. Its guarded
   mapping/source owner performs native calls and oracle comparison. Retain
   canonical input/output-state, mask and summary digests, block/tail coverage,
   actual invocation count, package operation identity and selected generation.
   Never infer execution from requested ISA, a successful load or a boolean.
5. Finish/cancel the package operation, close the source session and release the
   operation build-use in reverse ownership order. Cleanup failure quarantines
   the record and retains every outstanding resource for bounded explicit retry;
   it issues no usable token. The startup/session generation retention remains
   separately live through frontend admission and its cache decision.
6. Only a fully completed and cleaned operation reaches `Ready` and returns a
   `FrontendAdvisoryExecutionTokenV1`. `frontend_advisory_execution_consume_v1`
   checks owner/epoch, independent request identity, live startup binding and
   exact terminal record, then atomically changes `Ready` to `Consumed` once.
   It returns an immutable diagnostic projection; that projection is not reusable
   authority. Wrong-owner, stale, substituted and replayed tokens fail closed.

States: `Reserved → Executing → CleanupPending → Ready → Consumed`.
Failures enter `CleanupPending` or terminal `Rejected`; cancellation never
skips cleanup. A startup close rejects new work, drains retained uses, and makes
unconsumed tokens stale. Reclaimed record slots never recycle operation IDs;
counter exhaustion rejects. Proposed owner bounds are 64 outstanding records,
including quarantined and ready records, and 64 copied terminal diagnostics.
Input/block limits inherit the stricter existing package bounds. Evicting a
diagnostic cannot revive consumed authority or discard pending cleanup.

## Frontend policy and cache behavior

| Policy | Successful eligible operation | Unavailable, mismatched or failed operation |
|---|---|---|
| Reference | Bypass provider machinery; unchanged parser path | No provider dependency |
| PreferSimd | Consume token, then run the reference semantic parser | Discard all partial provider output; typed reference fallback only after resources are safely retired or quarantined |
| RequireSimd | Consume actual execution evidence, then run reference parser | Return explicit error before parser/cache admission; no silent fallback |

The existing adapter treats fewer than 32 bytes as no complete SIMD work:
Prefer may use a truthful scalar tail; Require remains unavailable under this
milestone. Changing that policy requires explicit contract review. Cleanup
quarantine remains bounded and cannot be mislabeled successful retirement.

The provider never changes source, parser globals, AST/HIR, diagnostic order,
interpolation/placeholder transforms or streaming promotion. Preserve
`classifier_only`, scalar lexical resolution and `reference_frontend_required`.
No GPU initialization is permitted on this route.

Startup performs the bounded catalog/selection pass once. Request dispatch uses
the retained typed binding directly: no per-request catalog scan, environment
parse, symbol lookup or subprocess. Record cold startup and warm direct dispatch
separately; source hashing and lifecycle work are per batch, never per element.

Keep startup cache V2 work in its existing owner lane. This milestone consumes
its authoritative identity rather than adding a second encoder. Bind stable
source/semantic, policy, provider/artifact and environment generations and the
typed fallback outcome through that owner; exclude per-operation IDs and timing
from semantic cache keys. Until the canonical identity join is available, bypass
provider-selected parse-cache reuse. A cache hit cannot satisfy Require by
replaying a prior execution token: dispatch/consumption precede restore. Retain
the startup generation through lookup/materialization; revocation invalidates
the decision. Reference cache behavior remains unchanged.

## Verification and performance ceiling

The [focused test plan](../../03_plan/sys_test/frontend_advisory_execution_authority_v1.md)
defines positive native invocation, substitution/replay, cleanup retry, parser
parity and latency gates. Measure request hashing, session creation, native call,
oracle, cleanup, consumption and reference parsing separately; include all of
them in end-to-end latency. Repeated semantic oracle work may prevent speedup:
do not hide it or promote this authority milestone as an optimization.

Retain NFR-002 selection p95 limits (1 ms warm, 25 ms cold), NFR-003 dispatch
overhead (2%), NFR-004 same-machine speedup (1.15x), and NFR-005 RSS limits (5%
selected, 2 MiB unselected). These are qualification gates, not current results.
Name hardware, runtime/artifact hashes and fixture corpus before measuring.
No full bootstrap is required for design review. Runtime acceptance remains
`MissingEvidence` until an admitted source-matched runner and compatible native
provider fixture execute the production path.
