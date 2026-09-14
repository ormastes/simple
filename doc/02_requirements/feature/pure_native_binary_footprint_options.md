<!-- codex-research -->
# Pure-native binary footprint — feature requirement options

Status: **UNSELECTED OPTIONS — not for integration.**  The user must select an
option before final requirements are written.  Do not create
`pure_native_binary_footprint.md` from `901b3fa290c`: that commit is unselected
draft evidence and cannot authorize implementation.

## Safety invariants for every option

Every option preserves the essential native boundaries: mmap/executable mapping,
W^X, relocation/raw calls, OS TLS/trust-store/socket leaves, GPU/device APIs,
window/display/event backends, audio/browser/backend loading, and foreign ABI
marshalling.  Pure Simple may own higher-level policy; no option replaces an
unavailable native capability with a success stub.  Existing public imports and
typed unavailable-capability errors remain compatible until separately proven.

Every option must also add the missing evidence fields before an optimization
claim: authoritative audit invocation/scope/receipt identity; versioned input,
runtime, provider, workload, and link manifests; canonical provider and dynamic
dependency rows; per-segment file/memory accounting; tool/reader/evaluator
identity; candidate command/cache labels; budgets; and sealed receipt identity.
A pair-level admission receipt must bind immutable source-matched control and
candidate receipts, profile/workload manifest references, evaluator-policy
digest, and individual NFR verdicts.  “One dynamic-loader owner” is limited to
the generic runtime ABI owner; backend-specific GPU/window/etc. loaders remain
essential native boundaries.

## F-1 — Evidence and manifest foundation first

Define one versioned footprint-manifest and owner-issued receipt contract, then
make the current audit/check paths emit and verify it.  Measure only existing
control/candidate artifacts; do not change provider ownership, I/O facades, or
runtime selection in this option.

- Pros: fixes the immediate evidence gap; lowest compatibility risk; turns
  historical counts and draft hypotheses into falsifiable inputs; gives later
  packets a stable audit and receipt interface.
- Cons: does not itself reduce binary bytes; exposes missing measurements before
  it can demonstrate an optimization; requires agreement on canonical schema.
- Effort: M — roughly 10–18 files (receipt/manifest/checker/tests/docs).

## F-2 — Exact ordinary closure after the evidence foundation

Implement F-1, then make ordinary native and Stage4 static links consume one
typed, prevalidated provider manifest and fixed-point requested-symbol closure.
`native_all`, bootstrap, host-GPU, and legacy profiles remain explicit named
lanes.  Missing, duplicate, stale, or unresolved ownership fails closed.

- Pros: directly prevents unrequested GPU/window/audio/browser/TLS/compiler
  providers from entering a minimal closure; makes link reasons reproducible;
  preserves native leaves while reducing accidental linkage.
- Cons: high compiler/linker integration risk; requires migration/shadow parity
  and careful cache invalidation; does not by itself consolidate duplicate app
  FFI or lazy-load compiler bytes.
- Effort: L — roughly 22–38 files (compiler closure, manifests, receipt,
  fixtures, unit/integration/system/performance tests, docs).

## F-3 — Full staged ownership and lazy-provider program

Adopt F-2 and additionally migrate duplicate app I/O declarations to one owner
with compatibility facades, make the interpreter app layer consume lower
capabilities, consolidate the dynamic-loader C owner, and activate the existing
typed native-build interface as an admitted lazy, process-pinned compiler
provider.  Stage4 dynamic-runtime remains a measured candidate, not a default,
until evidence admits it.

- Pros: addresses the broadest accidental closure and duplicate-owner sources;
  improves idle footprint for non-build commands; creates clear rollback packets
  while retaining all named native capability boundaries.
- Cons: widest compatibility and rollout surface; needs multiple independently
  reversible packets; cannot use historical size numbers as acceptance evidence;
  may reveal APIs whose compatibility must be deferred.
- Effort: XL — roughly 45–80 files across app, compiler, lib/runtime, audits,
  fixtures, specs, and documents.

## Decision guide

Choose F-1 to repair evidence before changing production selection; choose F-2
when exact native closure is the priority; choose F-3 only when the broader
ownership and lazy-provider migration is intended.  F-2 and F-3 include F-1;
they do not permit skipping its manifest/receipt work.
