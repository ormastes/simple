# Process capture raw-registry oracle depends on runtime composition

Status: source-only diagnostic fixture; native execution UNRUN. This follow-up
does not close [PR #7337](https://github.com/ormastes/simple/pull/7337) or the
Windows native-all missing-provider bug. It changes no production code.

## Preserved failure and owner

PR #7337 head `26c80e995b1c49f03262fa7f1a712f8431790603` records six exhausted
attempts. The last compiled and linked the actual consumer fixture, then
failed execution with exit14 and empty stdout/stderr. That exit means a saved
raw-word observation was not three; the actual count was not printed, and
the target linked-runtime identity remains UNKNOWN. The consumer had already
been called before this saved observation was checked.

The original fixture is
`test/fixtures/compiler/process_capture_owned_block/main.spl` at that PR head.
Its source SHA256 is
`a137e1db8083af56aabb50ec4d8f41f4ab53c344c781527c6e712432d9fdc443`;
the reported caller executable SHA256 is
`8bd262180bb590dde0e8ba0dd104aafcc3b5749d2d4b1bd1b8754c91b6d614a7`.
The original fixture, receipts, production patch and active draft are untouched.
The Windows owner retains evidence under
`C:/dev/simple/.git/worktrees/nativeall-process-capture-d88f/evidence/`, including
`linux-process-capture-2a484-attempt5/receipt.sdn` for logical attempt6.

The new fixture is
`test/fixtures/compiler/process_capture_canonical_owned_block/main.spl`.
Its introduction does not reset the old attempt budget or authorize execution.

## Exact-source explanation

At the original PR head, `src/runtime/runtime_memory.c:133` forwards raw
allocation registration into the canonical runtime owner when compiled with
`SIMPLE_RUNTIME_MEMORY_OWNER=1`. Its `rt_transient_raw_scope_begin` at line162
only sets the local raw-scope flags.

`src/runtime/runtime_native.c:2187` accepts a nonnull allocation without
registering it when `rt_core_transient_array_scope_active` is false. Only
canonical `rt_transient_array_scope_begin` at line1967 activates that scope.
Consequently the raw-word query at `runtime_memory.c:175` can return minus one
for a valid fresh 24-byte block after the original raw-only scope setup.

The compiler's C bundle defines `SIMPLE_RUNTIME_MEMORY_OWNER=1` in
`src/compiler/70.backend/backend/runtime_compiler.spl:993,1038` at that head.
The Rust runtime-only tests use runtime_memory.c without runtime_native.c and
can therefore pass with the local raw scope. The runtime-only result does not
qualify the canonical C composition or Windows native-all composition.

This is a source-proven difference between compositions. It is a conditional
explanation for exit14, not an attribution to the unknown retained executable.
No evidence here justifies a production allocation or capture semantic change.

## Canonical fixture contract

The new fixture refuses inherited module/session ownership, missing hardening,
missing declared provenance, or the wrong declared runtime composition. Its
actual process call and actual consumer remain the production implementations.
It reuses the existing bool-returning `transient_scope_begin`,
`transient_scope_pause` and `transient_scope_end` wrappers, whose physical C
array-scope ABI is i8. The raw-word query is i64. No competing scope signature
is introduced merely to observe the native lifecycle.

Setup completes before begin. Both the real child-result block and the
invalid-text block are allocated while the canonical array scope is active.
The fixture records their word counts, pauses the scope, prints the counts and
refuses an unexpected layout before dereferencing it in the consumer. It then
consumes both blocks and records their post-consumption counts. Copied managed text and
consumer tuple temporaries are created while paused. Scope teardown reclaims
the provider's original scope-owned payloads, while the copies survive for
post-teardown assertions. The fixture does not end a scope owned by a caller.

In general, paused allocations belong to a surrounding session if one exists,
otherwise scope zero; this standalone fixture rejects an inherited session.
It must preserve actual stdout/stderr, signed status7, the invalid-text error,
three-word observations before consumption, and minus-one observations after
consumption. Printed observations identify stages and actual counts rather
than reporting an unexplained status14.

The source baseline `05c57b4368292f3df439c76cd94d4307d9311d77` does not contain
PR #7337's consumer `rt_free` changes. The new fixture deliberately retains
unconditional release assertions and will expose that missing dependency;
it does not free the tested blocks on behalf of the consumer or fake a pass.
Root must coordinate the existing owner's production change separately.

## Provenance required before a future authorized run

The fixture accepts these declared inputs:

- `SIMPLE_PROCESS_CAPTURE_RUNTIME_COMPOSITION=canonical-c-memory-owner-v1`
- `SIMPLE_PROCESS_CAPTURE_RUNTIME_SHA256`: lowercase 64-digit SHA256 of the
  selected runtime archive, or of an exact multi-object runtime manifest.
- `SIMPLE_PROCESS_CAPTURE_ATTESTATION_SHA256`: lowercase 64-digit SHA256 of
  the externally verified SDN provenance record described below.

Syntax validation and printed declarations are not verification of a link.
An external reviewer must verify the record against actual artifacts before
execution. The SDN record must bind fixture source digest; producer binary and
source identities; target triple; final executable digest; exact linker
command/map; runtime archive/member or object paths and digests; owner symbols
for `rt_alloc`, `rt_free`, raw query, array scope and process tuple provider;
and the `SIMPLE_RUNTIME_MEMORY_OWNER=1` compile definition. If an archive is not
the complete runtime, hash a manifest of every selected runtime input rather
than presenting one member as the whole provider identity.

Retain actual stdout, stderr, exit status and all printed observations beside
that record. Missing or mismatched provenance remains UNKNOWN/BLOCKED. Do not
claim a supplied digest proves the fixture's linked implementation, and do not
substitute producer identity for target runtime identity.

## Artifact-access audit and validation limits

Read-only GitHub inspection on 2026-11-07 found no artifacts in PR-head runs
42263180584, 42263180434 and 42263180340. Older Windows run42208248396 has ladder
artifacts, including diagnostics artifact13501316100, but binds source
`04c3470126023edd7ef19c0e89576dff5dce812a`; it does not establish the later Linux
attempt6 caller's link identity. Its large archive was not downloaded merely
to substitute unrelated evidence. The documented Windows evidence directory
is inaccessible on this Linux host. A bounded local filename inventory did
not locate an attempt6 receipt or executable; this is not an exhaustive disk
forensic claim.

Source review by Astra and Sol checked the composition contract, i8 scope ABI,
ownership sequence, fail-closed provenance declarations and dependency limits.
The source-only SFFI backlog audit exposed three needless scope-signature
variants in the first fixture version. Reusing the existing transient wrappers
removed those variants: the aggregate inventory changed from403/399 to400/399
source variants, but its prerequisite still FAILs (migration3769/3546 after the
change). This is not a passing aggregate SFFI audit; neither this source-only
audit nor its queued migration count establishes runtime/link identity.
No compiler, native build or fixture execution was performed for this source
follow-up. Dynamic assertions, Windows native-all closure, source-matched
P2/SSpec and broader compiler/core/MCP qualification remain UNRUN. A source-only
landing is not release or compiler admission.

Before any native attempt, recover the retained caller/link metadata and
reconcile the exhausted budget with root and the original owner. A separately
authorized diagnostic needs a root build slot and isolated immutable inputs;
it must preserve the original six-attempt ledger and failed artifacts.
