<!-- codex-research -->
# SPipe Knowledge Compiler — Host Authority Provider Options

**Status:** Decision required; no option is selected
**Date:** 2026-08-27
**Scope:** P3 durable publication only
**Source facts:** research §43.8; architecture §21.10; detail design §12.10

## Decision boundary

P3 owns the journal, terminal/fence/current sequence, recovery, and read-open
authority.  Its private lexical `HostReplaceCurrentCapabilityV1` must perform
one fenced conditional replacement of `current` against either exact raw
predecessor bytes/digest or paired-null genesis, fsync the `current` parent
before reporting replacement, and preserve the closed mismatch/fatal algebra.
The recorded audit fact is narrower and sufficient: research §43.8 establishes
that P3 cannot manufacture this operation from normal Node filesystem
primitives; rename, link/unlink, write-then-compare, and advisory/user-space
locks are not substitutes. Node therefore denies before *any* P3 publication
mutation, including genesis. No platform provider is admitted by this record.

This document records alternatives only. It does not alter selected feature
requirements, authorize a fallback, or select an implementation.

## Option F1 — Transactional authority service

Provide a separately admitted, single authority-service owner for
`replaceCurrentIfExactV1`. P3 sends the exact closed request to that owner; the
owner serializes the compare-and-publish operation, durably records its own
linearizable decision, and exposes `current` only as a validated projection.
The service must still implement the exact P3 response/errno contract or map
its native outcomes into it without broadening it.

**Pros**

- Supplies one explicit linearization point instead of pretending a portable
  filesystem operation is CAS.
- Can support a uniform contract across hosts and centralize fencing, durable
  evidence, capability isolation, and auditability.
- Lets Node remain a dependency-free client/read-only host without becoming an
  unsafe publisher.

**Cons**

- Revises the direct-filesystem P3 deployment model and adds service lifecycle,
  availability, authentication, recovery, and operational ownership.
- A service crash, split-brain, or authority credential defect becomes a
  publication-security risk and needs dedicated failure/recovery proof.
- Adds RPC/storage latency and deployment overhead for otherwise local use.

**Effort:** XL; estimated 18–28 production/test/schema files plus a migration
of P3 publication/open/recovery evidence.

**Acceptance evidence**

- A hostile multi-client/SIGKILL test proves exactly one old-or-new complete
  authority state, no split brain, and P3's closed `replaced`, `mismatch`, and
  `SPK704` successor-absence outcomes.
- Durability/fence ordering, identity-bound authorization, restart recovery,
  and service-unavailable fail-closed behavior are independently verified.
- The Node client has no writable fallback and cannot install/select the
  authority service through environment, argv, globals, or a public factory.

## Option F2 — Platform-specific native provider

Admit `HostReplaceCurrentCapabilityV1` only on each platform where a native
provider can prove the exact raw-pointer conditional replacement, exclusive
fence, parent durability, closed errno mapping, and recovery semantics. All
other hosts, including normal Node, deny publication before mutation.

**Pros**

- Keeps the selected P3 direct durable-journal/current projection model.
- Avoids introducing a network/service dependency for local deployments.
- Can use platform-native durability and filesystem semantics where they are
  genuinely proven rather than emulated.

**Cons**

- No platform provider is admitted by the recorded Node audit; each native
  candidate needs platform-specific proof, not a claimed wrapper.
- Produces uneven availability and a costly platform-specific verification and
  release matrix.
- Kernel/filesystem/version differences can undermine portability or make
  latency/durability behavior hard to bound.

**Effort:** L–XL per admitted platform; estimated 10–18 files per provider,
plus native integration and destructive fault-injection fixtures. No estimate
counts unsupported platforms as complete.

**Acceptance evidence**

- For every admitted platform/filesystem/version tuple, a native adversarial
  test proves exact predecessor CAS (including paired-null genesis), exclusive
  fencing, fsync ordering, SIGKILL recovery, and the complete closed error map.
- A compatibility matrix proves all other tuples fail closed before P3 stages
  or mutates publication state; Node has no rename or test-seam fallback.
- Independent review verifies that the provider does not use advisory locking,
  TOCTOU read/replace, or a different response algebra.

## Option F3 — Defer mutable publication; continue offline work

Leave `HostReplaceCurrentCapabilityV1` unavailable and make P3 publication,
open authority, virtual MCP views, and materialization unavailable. Continue
only offline/read-only graph parsing, lexical search, diagnostics, schemas,
fixtures, and provider research that does not claim canonical published
authority.

**Pros**

- Preserves safety and portability immediately: no unsafe mutable path exists.
- Allows independent progress on deterministic, non-authoritative compiler
  components and a stronger corpus for eventual provider evaluation.
- Avoids operational cost until a truthful provider has evidence.

**Cons**

- Does not deliver the selected virtual view/read authority or P3 publication
  milestone; outputs must be explicitly non-canonical/offline.
- Delays end-to-end MCP list/read/search and transactional refactoring.
- Risks architectural drift if offline data is later treated as authority;
  strict boundary/labeling tests are required.

**Effort:** M; estimated 6–12 files to gate mutable/read-authority routes and
continue isolated offline components, plus future provider work.

**Acceptance evidence**

- Every P3 publish/open/recover and dependent MCP/materialization entry point
  deterministically reports unavailable before mutation or projection.
- Offline graph/search artifacts are namespaced and labeled non-authoritative;
  they cannot mint a P3 record, pointer, capability, or authorization receipt.
- Repeatable offline parsing/search diagnostics pass without a service/native
  provider, while attempted Node publication proves fail-closed.

## Selection requested

Choose exactly one feature direction (F1, F2, or F3). Final requirements may
be changed only after that user selection; unselected options must then be
removed rather than silently retained as normative behavior.
