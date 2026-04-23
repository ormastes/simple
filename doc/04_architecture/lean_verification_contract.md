# Lean Verification Contract

**Date:** 2026-04-04
**Status:** Active
**Scope:** Defines the supported Lean verification subset, state model, proof-unit model, and support matrix.

All agents and implementation phases work against this contract. Public documentation and claims must not exceed what is defined here.

## 1. Supported Verification Subset

### 1.1 In Scope (This Milestone)

| Feature | Syntax | Classification |
|---------|--------|---------------|
| `@verify` attribute | `@verify fn foo():` | stable |
| `@ghost` attribute | `@ghost fn helper():` | stable |
| `@trusted` attribute | `@trusted fn axiom():` | stable |
| Preconditions | `in: x > 0` | stable |
| Postconditions | `out(ret): ret > 0` | stable |
| Error postconditions | `out_err(err): err != nil` | supported_with_qualifiers |
| Invariants | `invariant: self.len >= 0` | stable |
| Decreases clauses | `decreases: n` | stable |
| `old()` expressions | `out(ret): ret > old(self.x)` | supported_with_qualifiers |
| Proof references | `proof uses: theorem_name` | supported_with_qualifiers |
| `lean{}` blocks | `lean { theorem ... }` | supported_with_qualifiers |
| External Lean modules | Import from `src/verification/proofs/` | stable |
| Ghost/spec-only functions | Pure, no side effects, erased at runtime | stable |
| Ghost erasure (MIR) | Ghost params/locals removed before codegen | stable |
| Lean code generation | Deterministic module emission | stable |
| Proof checking | Lean/Lake invocation with result capture | stable |

### 1.2 Out of Scope (Deferred)

| Feature | Reason |
|---------|--------|
| Loop invariants | Requires bounded loop analysis |
| Refinement types | Separate gated subset, too broad |
| Automatic proof synthesis | Research-grade, not productizable yet |
| Full dependent typing | Language-level change beyond verification |
| Replacing SSpec with proofs | Different concern (testing vs verification) |

### 1.3 Classification Definitions

- **stable**: Supported, tested, documented. Part of the public claim.
- **supported_with_qualifiers**: Real and supported, with explicit restrictions documented.
- **experimental**: Present but not part of the finished public claim.
- **out_of_scope**: Intentionally excluded from this milestone.

## 2. Verification State Model

Every proof unit uses exactly one of these six states:

| State | Meaning | Invariant |
|-------|---------|-----------|
| `verified` | All obligations checked by Lean, no admits/trust | Never includes admitted or trusted obligations |
| `failed` | Proof check ran, at least one obligation failed | At least one theorem failed |
| `admitted` | Obligations remain via `sorry`/`admit` | Proof debt must be visible in reports |
| `trusted` | Obligations bypassed via `@trusted`/`assume` | Trust markers must be visible in reports |
| `stale` | Cached result exists but inputs changed | Overrides any previous state until re-check |
| `not_checked` | Lean artifacts may exist, proof check not run | Default state for new/unverified units |

### State Transition Rules

- `not_checked` -> `verified` | `failed` | `admitted` | `trusted` (after proof check)
- `verified` -> `stale` (on source/dep change)
- `failed` -> `stale` (on source/dep change)
- `admitted` -> `stale` (on source/dep change)
- `trusted` -> `stale` (on source/dep change)
- `stale` -> `verified` | `failed` | `admitted` | `trusted` (after re-check)
- Any state -> `not_checked` (on cache clear)

### Aggregation Rules

When rolling up states (file -> project), the most severe state wins:
`failed` > `admitted` > `trusted` > `stale` > `not_checked` > `verified`

## 3. Proof Unit Model

A proof unit is the atomic unit of verification tracking.

**Granularity:** File-level for v1. One proof unit per source file with `@verify` annotations.

| Field | Type | Description |
|-------|------|-------------|
| `source_file` | text | Originating `.spl` file |
| `source_symbol` | text | Primary symbol or `"*"` for file-level |
| `lean_module` | text | Generated Lean module path |
| `lean_file` | text | Filesystem path to `.lean` file |
| `obligations` | List&lt;text&gt; | Theorem/obligation names |
| `state` | VerificationState | Current state |
| `fingerprint` | text | Content hash |
| `dependencies` | List&lt;text&gt; | Imported proof module paths |
| `last_check` | Option&lt;text&gt; | ISO-8601 timestamp |
| `admitted_count` | i32 | sorry/admit count |
| `trusted_count` | i32 | assume/trusted count |

### Fingerprint Inputs

Cache key = hash of:
1. Source file content
2. Generated Lean content
3. Dependency file hashes (imported proof modules)
4. Lean toolchain version

Any change in these inputs marks the unit `stale`.

## 4. Semantic Separation

| Concern | Mechanism | Output |
|---------|-----------|--------|
| Runtime contract checking | `in:`/`out:` compiled to runtime checks | Cranelift IR with `simple_contract_check()` |
| Generated proof obligations | `@verify` + contracts -> Lean theorems | `.lean` files with `theorem` + `sorry` stubs |
| Embedded Lean authoring | `lean{}` blocks | Verbatim Lean in generated modules |
| External Lean proofs | `proof uses:` references | Import from `src/verification/proofs/` |
| Ghost/spec code | `@ghost` functions, spec-only params | Erased at MIR level, present in Lean |

Runtime and verification concerns are independent:
- A function can have runtime contracts WITHOUT `@verify` (runtime-only checking)
- A function can have `@verify` WITHOUT runtime contracts (proof-only obligations)
- Both can coexist (runtime checks + formal proof)

## 5. Support Matrix

| Feature | Generation | Proof Check | Reporting | Cache | Classification | Known Limits |
|---------|-----------|-------------|-----------|-------|---------------|-------------|
| `@verify` basic | Yes | Yes | Yes | Yes | stable | Pure functions only |
| `@ghost` functions | Yes | Yes | Yes | Yes | stable | Must be pure |
| `@trusted` bypass | Yes | N/A | Yes (marked) | Yes | stable | — |
| `in:` preconditions | Yes | Yes | Yes | Yes | stable | — |
| `out:` postconditions | Yes | Yes | Yes | Yes | stable | — |
| `out_err:` error post | Yes | Yes | Yes | Yes | qualified | Limited expression forms |
| `invariant:` | Yes | Yes | Yes | Yes | stable | Class invariants only |
| `decreases:` | Yes | Yes | Yes | Yes | stable | Single measure |
| `old()` expressions | Yes | Partial | Yes | Yes | qualified | Simple field access only |
| `proof uses:` | Yes | Yes | Yes | Yes | qualified | Manual theorem matching |
| `lean{}` blocks | Yes | Yes | Yes | Yes | qualified | Module-level only for v1 |
| External proofs | Yes | Yes | Yes | Yes | stable | — |
| Incremental cache | — | — | — | Yes | stable | File-level granularity |
| CLI reporting | — | — | Yes | — | stable | — |
| Machine-readable report | — | — | Yes | — | stable | SDN format |

## 6. Authoritative Commands

| Command | Purpose |
|---------|---------|
| `simple gen-lean generate` | Output Lean code to stdout |
| `simple gen-lean write` | Write generated Lean files to `src/verification/` |
| `simple gen-lean compare` | Diff generated vs existing, check completeness |
| `simple gen-lean verify` | Run Lean and fail on errors/sorry |
| `simple verify status` | Show Lean availability and artifact inventory |
| `simple verify check` | Verify all proofs |
| `simple verify list` | List verification artifacts |

## 7. Toolchain Policy

- **Lean:** Version pinned in `lean-toolchain` file
- **Lake:** Must match Lean version compatibility
- **Mathlib:** Optional dependency, version pinned in `lakefile.lean`
- Environment failures (missing Lean, wrong version) are reported distinctly from proof failures
