# AOP Completion Plan

**Date:** 2026-04-04  
**Status:** Draft  
**Scope:** Complete the AOP implementation so it moves from a verified baseline plus partial authoring surface to a finished, evidence-backed feature.

## 1. Current Classification

AOP is **partial, not experimental**.

Why it is partial:
- the repo already has a real predicate-based AOP design
- runtime-facing proceed enforcement and `init(...)` interception are already proven
- weaving concepts, verification errors, and security-AOP design are present
- the remaining work is to complete the higher-level authoring and weaving surface without regressing the current baseline

Why it is not experimental:
- this is not just a proposal with empty scaffolding
- there is already end-to-end evidence for a scoped runtime/compiler slice
- the feature gap is breadth and completion of the authoring/weaving system, not existence

## 2. Completion Target

The feature is complete when the repo can truthfully state:

> AOP provides a finished predicate-based aspect system with explicit pointcuts, before/after/around advice, deterministic weaving order, verified proceed enforcement, compile-time weaving as the base backend, and scoped runtime interception where explicitly supported.

This does **not** require every optional backend to be equally mature.

It **does** require:
- stable pointcut authoring
- stable advice authoring
- deterministic weaving order
- authoritative compile-time weaving path
- scoped runtime interception with explicit policy
- clear verification and diagnostics

## 3. Current Gaps

### 3.1 The runtime/compiler baseline is real, but the authoring surface is incomplete

Current issue:
- design and research docs define the intended AOP model
- repo evidence currently proves only a narrower slice of actual end-to-end behavior

Completion requirement:
- make the public authoring surface complete enough that users can define aspects without relying on internal-only or design-only conventions

### 3.2 Pointcut support needs a finished supported-selector contract

Current issue:
- the unified predicate grammar exists as the semantic design reference
- the repo needs a clear implemented subset for AOP pointcuts

Completion requirement:
- explicitly define the supported pointcut selectors for the finished milestone
- reject unsupported selectors with deterministic diagnostics

### 3.3 Advice forms need full implementation and proof

Current issue:
- before/after/around semantics are designed
- around/proceed invariants are partially proven
- the full set of supported advice kinds is not yet clearly finished as a repo feature

Completion requirement:
- define the implemented advice kinds
- prove correct behavior and ordering for each

### 3.4 Compile-time weaving is the intended base, but the implemented closure is unclear

Current issue:
- design docs strongly prefer compile-time weaving as the base backend
- the repo still needs a finished implementation story that clearly distinguishes:
  - compile-time weaving
  - optional runtime interception
  - unsupported or deferred join points

Completion requirement:
- compile-time weaving must be the authoritative public implementation
- runtime interception must remain scoped and explicit

### 3.5 Diagnostics and verification need to match the supported AOP subset

Current issue:
- verification error families already exist
- planned AOP diagnostics exist
- implementation and docs need a tighter mapping between what is supported and which errors users see

Completion requirement:
- unsupported pointcuts, invalid advice ordering, and proceed misuse must fail clearly

## 4. Final Feature Model

### 4.1 Predicate-based pointcuts

The completion milestone should support a scoped selector set:
- `execution(...)`
- `within(...)`
- `attr(...)`
- optionally `effect(...)` if already wired enough to prove

Recommended rule:
- finish a compact, defensible subset first
- leave high-volume or deferred selectors explicitly out of scope

Do not complete this milestone by pretending all designed selectors are equally implemented.

### 4.2 Advice kinds

Required finished advice kinds:
- `before`
- `after_success`
- `after_error`
- `around`

For each advice kind, the system must define:
- when it runs
- what context it receives
- whether it may change return/error flow
- ordering relative to other advice

### 4.3 Weaving backends

Required completion model:
- compile-time weaving is the base supported backend
- runtime interception remains allowed only in explicit, scoped cases such as container-controlled construction
- link-time weaving remains optional and outside the core completion milestone unless already proven

### 4.4 Determinism

Required resolution order:
- priority
- specificity
- stable order

This must be implemented, not only documented.

## 5. Implementation Phases

### Phase 1. Define the supported AOP subset

Goal:
- remove ambiguity between the full design and the implemented milestone

Tasks:
- declare which selectors are part of the finished AOP subset
- declare which advice kinds are fully supported
- declare which join point categories are deferred

Suggested first-class subset:
- `execution`
- `within`
- `attr`
- `before`
- `after_success`
- `after_error`
- `around`

Deferred by default:
- general `get` / `set`
- broad wildcard-heavy runtime join points
- nonessential runtime backends beyond explicit allowlisted scopes

Exit criteria:
- one short support contract exists in docs and tests

### Phase 2. Finish pointcut parsing and validation

Goal:
- make authoring predictable and diagnosable

Tasks:
- ensure `pc{...}` parsing supports the finished selector subset
- reject unsupported selectors with dedicated diagnostics
- enforce operator precedence and wildcard rules consistently

Required diagnostics:
- invalid pointcut syntax
- undefined join point
- invalid selector
- wildcard misuse where verification rules forbid it

Exit criteria:
- pointcut parsing and validation are fully covered for the supported subset

### Phase 3. Finish advice semantics and proceed enforcement

Goal:
- make advice behavior complete and safe

Tasks:
- implement and verify behavior for before/after_success/after_error/around
- enforce `proceed()` exactly-once or the chosen invariant for around advice
- define whether around advice may rewrite return values and errors

Required tests:
- before advice runs before the target
- after_success runs only on success
- after_error runs only on failure
- around advice must call `proceed()` according to policy
- nested around advice respects deterministic ordering

Exit criteria:
- every supported advice kind has passing semantic tests

### Phase 4. Make compile-time weaving authoritative

Goal:
- complete the base weaving backend

Tasks:
- finish MIR-level or equivalent compile-time advice insertion for the supported subset
- ensure woven code preserves semantics when no aspects are enabled
- ensure zero overhead when AOP is disabled, per the design contract

Required tests:
- empty aspect config produces no probes or weaving metadata
- matching pointcuts insert advice deterministically
- non-matching pointcuts leave the target unchanged

Exit criteria:
- compile-time weaving is the repo’s authoritative AOP path

### Phase 5. Scope and finish runtime interception

Goal:
- keep runtime interception real but narrowly governed

Tasks:
- define the allowed runtime join points
- gate runtime interception behind explicit allowlists or profile/config policy
- prevent release-mode surprise interception unless explicitly enabled

Required tests:
- `init(...)` interception works only where allowed
- runtime interception disabled means raw instance return with no proxy overhead
- release-mode restrictions are enforced

Exit criteria:
- runtime interception is supported as a scoped feature, not an open-ended fallback

### Phase 6. Finish deterministic ordering and conflict handling

Goal:
- make multiple aspects predictable

Tasks:
- implement priority/specificity/stable-order resolution
- detect conflicting advice order where required
- document tie-breaking behavior

Required tests:
- two aspects with different priorities run in the correct order
- equal-priority cases resolve deterministically
- conflicting advice ordering emits a clear diagnostic if the model forbids it

Exit criteria:
- aspect ordering is deterministic and tested

### Phase 7. Align verification, diagnostics, and security AOP

Goal:
- make the supported subset safe in verified and security-sensitive contexts

Tasks:
- wire the implemented AOP subset to the existing verification error family
- ensure security AOP examples only use supported join points and advice forms
- keep ghost/verified restrictions enforceable

Required tests:
- verified code rejects disallowed non-ghost aspects
- wildcard restrictions in verified pointcuts are enforced
- security-AOP sample rules validate and weave correctly for the supported subset

Exit criteria:
- verification and security docs describe the same AOP subset the implementation supports

### Phase 8. Publish machine-readable aspect support metadata

Goal:
- make AOP support auditable

Tasks:
- publish the supported selector/advice matrix
- classify selectors as:
  - supported
  - scoped
  - deferred
- classify backends as:
  - compile-time supported
  - runtime scoped
  - optional/deferred

Exit criteria:
- README and guide wording can reference one source of truth

## 6. Test Plan

### 6.1 Parsing and validation

Required:
- valid `pc{...}` parsing for the supported subset
- precedence and grouping tests
- selector-specific validation tests
- unsupported selector rejection tests

### 6.2 Advice semantics

Required:
- before advice semantics
- after_success semantics
- after_error semantics
- around/proceed invariants
- nested advice ordering

### 6.3 Weaving correctness

Required:
- compile-time weaving inserts advice at the right join points
- non-matching code remains unchanged
- zero-overhead path when AOP disabled

### 6.4 Runtime interception

Required:
- explicit init interception proof
- disabled runtime interception proof
- release restrictions / allowlist enforcement

### 6.5 Verification and security constraints

Required:
- AOP verification errors trigger on prohibited verified-context usage
- security-AOP sample rules validate against the supported subset

## 7. Documentation Plan

Update:
- research/spec reference for supported subset
- AOP guide docs
- security AOP docs
- diagnostics docs
- README feature wording

Required public wording after completion:
- AOP is predicate-based and compile-time-first
- runtime interception is scoped, not universal
- supported selectors/advice kinds are named explicitly

## 8. NFR Targets

### Correctness

- advice ordering must be deterministic
- proceed invariants must be enforced
- unsupported selectors must fail clearly

### Performance

- zero overhead when AOP is disabled
- no unnecessary runtime proxying when runtime interception is off

### Maintainability

- selector support must be centralized
- diagnostics must derive from implemented support, not only design intent
- docs must distinguish supported versus deferred join points

## 9. Recommended Public State After Completion

After Phases 1 through 7 are complete, the repo can describe AOP as:

- predicate-based pointcuts over a supported selector subset
- compile-time weaving as the default execution model
- deterministic before/after/around advice
- scoped runtime interception for explicitly supported join points
- verification-aware AOP constraints

At that point AOP moves from:
- partial

to:
- complete with a clearly bounded support model

## 10. Immediate Next Steps

1. Write the supported selector/advice subset as an explicit contract.
2. Finish pointcut parsing/validation for that subset.
3. Finish advice semantics and proceed enforcement across all supported advice kinds.
4. Make compile-time weaving the clearly authoritative path in tests and docs.
5. Align runtime interception, diagnostics, and verification rules with the same supported subset.
