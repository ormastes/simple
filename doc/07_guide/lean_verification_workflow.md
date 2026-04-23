# Lean Verification Workflow Guide

**Status:** Active
**Date:** 2026-04-04
**Contract:** [doc/04_architecture/lean_verification_contract.md](../04_architecture/lean_verification_contract.md)

This guide describes how to use the Simple compiler's Lean 4 formal verification workflow. The workflow translates annotated Simple source code into Lean 4 proof obligations, checks them with the Lean toolchain, caches results incrementally, and reports verification status at multiple levels.

---

## Quick Start

```bash
# 1. Install Lean 4 (stable channel)
curl -sSf https://raw.githubusercontent.com/leanprover/elan/main/elan-init.sh | sh

# 2. Check toolchain readiness
simple verify status

# 3. Generate Lean proof obligations from your annotated code
simple gen-lean write

# 4. Verify all generated proofs
simple verify check

# 5. View the verification report
simple verify list
```

### Minimal Verified Function

```simple
@verify
fn factorial(n: i64) -> i64:
    in: n >= 0
    out(ret): ret > 0
    decreases: n
    if n == 0:
        1
    else:
        n * factorial(n - 1)
```

Running `simple gen-lean write` produces a Lean 4 file with:
- A `theorem factorial_pre_0` for the precondition `n >= 0`
- A `theorem factorial_post_0` for the postcondition `ret > 0`
- A `decreases` annotation for termination

Running `simple verify check` invokes Lean/Lake to check these theorems. Unproven obligations use `sorry` and are reported as **admitted** (proof debt).

---

## Supported Verification Features

The verification workflow supports a bounded subset of formal verification. All features below are tested and documented. Deferred features are listed in [Known Limitations](#known-limitations).

### @verify Attribute

Marks a function for formal verification. The compiler generates Lean proof obligations from the function's contracts.

```simple
@verify
fn abs(x: i64) -> i64:
    out(ret): ret >= 0
    if x >= 0: x else: -x
```

**Classification:** stable
**Restriction:** Verified functions must be pure -- no IO, Net, Fs, or async effects (rule V-EFFECT). No `@unsafe` operations (rule V-UNSAFE). No reflection (rule V-REFLECT).

### Contracts (in:/out:/invariant:/decreases:)

Contracts specify preconditions, postconditions, invariants, and termination measures.

| Contract | Syntax | Purpose |
|----------|--------|---------|
| Precondition | `in: expr` | Must hold on function entry |
| Postcondition | `out(ret): expr` | Must hold on function exit; `ret` binds the return value |
| Error postcondition | `out_err(err): expr` | Must hold when function returns an error |
| Invariant | `invariant: expr` | Must hold for class/struct instances |
| Decreases | `decreases: expr` | Termination measure for recursive functions |
| Old expression | `old(expr)` | Refers to pre-call value in postconditions |

**Example with all contract types:**

```simple
class Counter:
    count: i64
    invariant: self.count >= 0

@verify
fn increment(c: Counter) -> Counter:
    in: c.count < 1000
    out(ret): ret.count == old(c.count) + 1
    Counter(count: c.count + 1)
```

**Qualifiers:**
- `out_err:` supports limited expression forms
- `old()` supports simple field access only (not arbitrary expressions)
- `invariant:` applies to class invariants only
- `decreases:` supports a single measure expression

### Ghost and Spec-Only Code (@ghost)

Ghost functions exist only for specification purposes. They are erased at the MIR level before codegen -- they produce no runtime code. Ghost functions must be pure and side-effect-free.

```simple
@ghost
fn sorted(xs: [i64]) -> bool:
    for i in 0..xs.len() - 1:
        if xs[i] > xs[i + 1]:
            return false
    true

@verify
fn insert_sorted(xs: [i64], x: i64) -> [i64]:
    in: sorted(xs)
    out(ret): sorted(ret)
    # ... implementation ...
```

**Classification:** stable
**Invariant:** Ghost params and locals are removed from MIR before codegen. They appear only in generated Lean modules.

### Trusted Code (@trusted)

Marks a function as axiomatically trusted. No proof obligations are generated -- the function's contracts are assumed to hold. This is **proof debt**, not verification.

```simple
@trusted
fn read_file(path: text) -> text:
    in: path.len() > 0
    out(ret): ret.len() >= 0
    # FFI call to OS -- cannot be verified
    rt_file_read_text(path)
```

**Classification:** stable
**Rule V-TRUSTED:** Trusted boundary functions must have contracts. A `@trusted` function without contracts triggers a verification warning.
**Reports always show trusted count prominently.** Trusted is never displayed as "verified."

### Embedded Lean Blocks (lean{})

Embed raw Lean 4 code directly in Simple source. The content is included verbatim in the generated Lean module. Imports within `lean{}` blocks are deduplicated with the generator's default imports.

```simple
lean {
    import Mathlib.Tactic

    theorem helper_lemma (n : Nat) : n + 0 = n := by simp
}
```

**Classification:** supported_with_qualifiers
**Restrictions:**
- Module-level placement only for v1 (not inside function bodies)
- Namespace collision detection: if a `lean{}` block defines a theorem with the same name as a generated obligation, a collision warning is emitted
- Import lines inside `lean{}` blocks are stripped from the body and merged into the top-level import section

### External Proof References (proof uses:)

Reference a theorem defined in an external Lean file under `src/verification/proofs/`.

```simple
@verify
fn gcd(a: i64, b: i64) -> i64:
    in: a > 0
    in: b > 0
    out(ret): ret > 0
    proof uses: gcd_positive_theorem
    # ...
```

The compiler resolves the reference by searching for `gcd_positive_theorem` in external Lean modules and imports it into the generated proof module.

**Classification:** supported_with_qualifiers
**Restriction:** Theorem matching is manual -- the theorem name must exactly match what is defined in the external file.

---

## Verification Commands

All commands use the `simple` binary. No subprocess calls are needed.

### Generation Commands

| Command | Purpose |
|---------|---------|
| `simple gen-lean generate` | Output generated Lean code to stdout (does not write files) |
| `simple gen-lean write` | Write generated Lean files to `src/verification/` directory |
| `simple gen-lean compare` | Diff generated vs existing Lean files; check completeness |
| `simple gen-lean verify` | Run Lean/Lake on generated files and fail on errors/sorry |

### Verification Commands

| Command | Purpose |
|---------|---------|
| `simple verify status` | Show Lean toolchain availability and verification artifact inventory |
| `simple verify check` | Verify all proof obligations using Lean/Lake |
| `simple verify list` | List all verification artifacts and their current state |

### Typical Workflow

```bash
# After modifying @verify functions:
simple gen-lean write        # Regenerate Lean files
simple verify check          # Run proofs
simple verify list           # Review results
```

---

## Verification States

Every proof unit (file-level for v1) has exactly one of six states:

| State | Display | Meaning |
|-------|---------|---------|
| `verified` | Verified | All obligations checked by Lean with no admits or trust |
| `failed` | FAILED | Proof check ran and at least one obligation failed |
| `admitted` | Admitted (sorry) | Obligations remain via `sorry`/`admit` -- **proof debt** |
| `trusted` | Trusted (assume) | Obligations bypassed via `@trusted`/`assume` -- **proof debt** |
| `stale` | Stale | Cached result exists but inputs have changed since last check |
| `not_checked` | Not Checked | Lean artifacts may exist but proof check has not been run |

### State Transitions

```
not_checked  -->  verified | failed | admitted | trusted   (after proof check)
verified     -->  stale                                    (on source/dep change)
failed       -->  stale                                    (on source/dep change)
admitted     -->  stale                                    (on source/dep change)
trusted      -->  stale                                    (on source/dep change)
stale        -->  verified | failed | admitted | trusted   (after re-check)
any state    -->  not_checked                              (on cache clear)
```

### Aggregation

When rolling up states from file level to project level, the most severe state wins:

`failed` > `admitted` > `trusted` > `stale` > `not_checked` > `verified`

A project reports `verified` only when **every** proof unit is individually `verified`.

### Admitted and Trusted are Proof Debt

**Admitted** means the obligation contains `sorry` or `admit` -- Lean accepts the file but the theorem is not actually proven. This is proof debt that must be resolved before claiming full verification.

**Trusted** means the obligation is axiomatically assumed via `@trusted` or `assume`. The function's contracts are not checked by Lean. This is appropriate for FFI boundaries but is still proof debt.

Reports always show admitted and trusted counts prominently. Neither state is ever rendered as "verified" or displayed with success styling.

---

## Cache and Incremental Verification

### Cache Location

Verification results are cached in `build/verification-cache/`. This directory is git-ignored.

### Fingerprint Inputs

A cache entry's fingerprint is computed from:

1. **Source file content** -- the `.spl` file with `@verify` annotations
2. **Generated Lean content** -- the `.lean` file produced by `gen-lean write`
3. **Dependency file hashes** -- imported proof module paths
4. **Lean toolchain version** -- from `lean-toolchain` file

Any change in these inputs marks the proof unit as `stale`.

### Invalidation Rules

- Editing a source file invalidates its own cache entry
- Editing an external proof module invalidates all proof units that depend on it
- Changing the Lean toolchain version invalidates all cache entries
- Running `simple verify check` after invalidation re-checks affected units
- Stale entries are never returned from cache lookups (safety invariant)

### Cache Format

Each entry is stored as an SDN file (one per source file) containing:
- fingerprint hash
- verification state
- per-theorem results (proven/failed/admitted)
- ISO-8601 timestamp
- Lean version
- source file path

### Cache Statistics

After running `simple verify check`, cache performance is reported:
- Total entries, hits, misses, stale count, hit rate percentage

---

## Reporting and Diagnostics

Verification reports are available at four levels of detail:

| Level | Shows |
|-------|-------|
| **Project** | One-line summary: "3 verified, 1 failed, 2 admitted" |
| **File** | Per-file state with obligation counts and debt markers |
| **Symbol** | Per-function/type verification state |
| **Theorem** | Individual theorem detail with source origin and Lean file path |

### Report Features

- **Debt visibility:** Admitted and trusted counts are always shown prominently with `[N sorry]` and `[N assume]` markers
- **Error separation:** Environment errors (missing Lean, wrong version) are reported separately from proof failures
- **Machine-readable output:** Reports can be rendered in SDN format for tool integration
- **Source tracing:** Failed theorems include source file and line number

### Environment vs Proof Errors

The reporting system distinguishes between:
- **Environment errors:** Lean not found, version mismatch, Lake dependency failures. These indicate toolchain setup problems, not proof failures.
- **Proof errors:** Theorem check failures, `sorry` obligations, type errors in generated Lean. These indicate actual verification gaps.

---

## Known Limitations

### Deferred (Out of Scope for This Milestone)

| Feature | Reason |
|---------|--------|
| Loop invariants | Requires bounded loop analysis |
| Refinement types | Separate gated subset, too broad for this milestone |
| Automatic proof synthesis | Research-grade, not productizable yet |
| Full dependent typing | Language-level change beyond the verification subset |
| Replacing SSpec with proofs | Different concern (testing vs verification) |

### Current Restrictions

- **File-level granularity:** Proof units are tracked per source file, not per function. Symbol-level granularity is planned for a follow-on milestone.
- **Pure functions only:** `@verify` functions must be pure. Functions with IO, Net, Fs, or async effects cannot be verified (use `@trusted` for FFI boundaries).
- **Single decreases measure:** Only one expression is supported per `decreases:` clause.
- **old() expressions:** Limited to simple field access (`old(self.x)`), not arbitrary nested expressions.
- **lean{} blocks:** Module-level placement only. Cannot embed Lean code inside function bodies.
- **Proof references:** Manual theorem name matching. No automatic resolution or fuzzy matching.
- **Error postconditions:** Limited expression forms supported.

---

## Examples

### Verified Arithmetic

```simple
@verify
fn add_positive(a: i64, b: i64) -> i64:
    in: a > 0
    in: b > 0
    out(ret): ret > a
    out(ret): ret > b
    a + b
```

### Ghost Specification with Trusted Boundary

```simple
@ghost
fn is_valid_path(path: text) -> bool:
    path.len() > 0 and not path.contains("..")

@trusted
fn safe_read(path: text) -> text:
    in: is_valid_path(path)
    out(ret): ret.len() >= 0
    rt_file_read_text(path)
```

### Embedded Lean Proof

```simple
@verify
fn double(n: i64) -> i64:
    in: n >= 0
    out(ret): ret == 2 * n
    n + n

lean {
    theorem double_correct (n : Int) (h : n >= 0) : n + n = 2 * n := by ring
}
```

### Class with Invariant

```simple
class BoundedBuffer:
    items: [i64]
    capacity: i64
    invariant: self.items.len() <= self.capacity
    invariant: self.capacity > 0

@verify
fn push(buf: BoundedBuffer, item: i64) -> BoundedBuffer:
    in: buf.items.len() < buf.capacity
    out(ret): ret.items.len() == old(buf.items.len()) + 1
    BoundedBuffer(items: buf.items.push(item), capacity: buf.capacity)
```

---

## Required Toolchain

- **Lean 4:** Version pinned in `lean-toolchain` (currently `leanprover/lean4:stable`)
- **Lake:** Installed automatically with Lean; must be compatible with the pinned Lean version
- **Mathlib:** Optional dependency, version pinned in `lakefile.lean` when used

Install Lean 4 via [elan](https://github.com/leanprover/elan):
```bash
curl -sSf https://raw.githubusercontent.com/leanprover/elan/main/elan-init.sh | sh
```

Check readiness:
```bash
simple verify status
```

The status command reports Lean availability, version match against `lean-toolchain`, and Lake availability.

---

## Reference

- **Contract:** [doc/04_architecture/lean_verification_contract.md](../04_architecture/lean_verification_contract.md) -- authoritative feature matrix and state model
- **Support matrix:** Section 5 of the contract document
- **Verification checker rules:** V-UNSAFE, V-EFFECT, V-REFLECT, V-GHOST, V-TRUSTED, V-PARTIAL
- **Cache directory:** `build/verification-cache/`
- **Generated Lean output:** `src/verification/` subdirectories
