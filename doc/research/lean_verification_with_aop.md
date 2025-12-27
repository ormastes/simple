# Simple Verification Mode (Lean) — Unified Specification

**Version:** 2025-12-28

This document defines a single, coherent verification mode for Simple that (1) generates Lean artifacts, (2) enforces a "verified subset" of the language, and (3) applies strict AOP and macro constraints so that the code you prove is the code you run.

---

## 1. Goals and Non-Goals

### 1.1 Goals

- Allow marking packages/modules/types/functions as Lean-checked ("verified").
- Generate Lean 4 code for verified declarations and emit proof obligations from contracts/invariants.
- Prevent cross-cutting transformations (AOP, macros) from silently changing verified semantics.

### 1.2 Non-Goals (Initial Milestone)

- Fully verified modeling of OS/FFI/concurrency/IEEE-float-bytes semantics.
- Automatic discharge of all proofs without user input.

---

## 2. Core Terminology

### 2.1 Verification Context

A declaration is in verification context ("Lean-checked") if it is:

1. Inside a package/module where verification is enabled by config, or
2. Annotated with `@verify`, or
3. A descendant (nested or inherited) of a verified type (see §3.3).

### 2.2 Ghost Code

Ghost code exists for specifications/instrumentation and must not affect runtime-observable behavior. Ghost state cannot be used to branch, allocate runtime resources, or change return values.

### 2.3 Trusted Boundary

A declaration marked `@trusted` is accepted as an assumption: it has a specification surface, but its implementation is not proven.

---

## 3. Enabling Verification Mode

### 3.1 Package-Level Enablement (`__init__.spl`)

A package may enable verification as a default:

```simple
# __init__.spl
package:
  verify: true
```

### 3.2 Build Configuration

A build config may enable verification globally (format is build-system defined):

```toml
[verify]
default = true
backend = "lean"
```

### 3.3 Propagation Rules ("Children" and Inheritance)

**Rule V-SCOPE**
If a scope has `verify=true`, then all lexical children (nested classes/enums, methods, local helpers) are Lean-checked unless explicitly annotated `@trusted` or `@unsafe`.

**Rule V-INHERIT** (mandatory)
If `class Base` is Lean-checked, any `class Derived : Base` is also Lean-checked. If a user attempts to opt out, compilation fails. (A non-verified override would invalidate Base's proven properties.)

---

## 4. Verification Annotations

### 4.1 Attributes

- `@verify` — declaration is Lean-checked (unless forbidden by config).
- `@trusted` — declaration is assumed correct; Lean sees only its spec surface.
- `@unsafe` — declaration is excluded from verification; cannot be depended on by verified code except through a `@trusted` spec boundary.
- `ghost` — marks ghost declarations (vars/functions/fields/modules).

### 4.2 Dependency Rule

**Rule V-DEP**
Lean-checked code may depend on non-verified code only through `@trusted` declarations (spec boundary).

---

## 5. Contracts, Invariants, and Termination

### 5.1 Contract Clauses

Lean-checked functions may declare:

- `requires:` — preconditions
- `ensures:` — postconditions (`result` allowed)
- `invariant:` — class invariant
- `decreases:` — termination metric for recursion
- `modifies:` — (optional initial milestone) frame/effects boundary for mutable state

**Example:**

```simple
@verify
class BankAccount:
  balance: Int

  invariant:
    balance >= 0

  fun deposit(amount: Int) -> BankAccount:
    requires: amount >= 0
    ensures: result.balance == self.balance + amount
    ensures: result.balance >= 0
    return self{ balance = self.balance + amount }
```

### 5.2 Termination Requirement (Lean-Driven)

Lean strongly distinguishes total definitions (accepted by termination checking) from definitions that rely on "unsafe" mechanisms. Lean requires termination arguments when measures are specified and requires proofs that recursive calls decrease.

**Rule V-TERM** (mandatory)
In Lean-checked code, recursion must be:

1. Structurally terminating, or
2. Provided with `decreases:` such that the compiler can translate it into Lean termination arguments.

General recursion without a termination argument is rejected.

---

## 6. Verified Subset Restrictions

This section defines language features that are disallowed (compile error) in Lean-checked contexts unless explicitly placed behind `@trusted` boundaries.

### 6.1 Unsafe Primitives and Observation of Runtime Internals

Lean explicitly notes that "unsafe" features can break assumptions about its equational theory (including unsafe casts, pointer/address equality checks, and refcount observation).

**Rule V-UNSAFE** (mandatory)
Disallow in Lean-checked code:

- Pointer/address equality / identity observation
- Unsafe casts / reinterpretation
- Refcount/exclusivity observation primitives
- Inline asm or raw memory manipulation

Allow only behind `@trusted` APIs with explicit specs.

### 6.2 Partiality / Nontermination

Lean's `partial` keyword is implemented via an auxiliary unsafe definition plus an opaque constant, and is intended for general recursion that may not terminate.

**Rule V-PARTIAL** (mandatory)
Lean-checked code must not rely on nontermination. Model partiality explicitly via:

- Sum types (`T | Err`) / `Option[T]`, or
- `@trusted` boundaries.

### 6.3 Effects: IO / Randomness / Time / Concurrency / FFI

**Rule V-EFFECT** (recommended default; mandatory for milestone-1)
Disallow in Lean-checked code:

- IO/syscalls, filesystem/network
- Randomness / system time
- Threads/async/concurrency primitives
- FFI/native bindings

Permit only via `@trusted` interfaces with specs.

### 6.4 Reflection / Dynamic Code Features

**Rule V-REFLECT** (recommended default)
Disallow:

- Reflection over members/types
- Runtime code loading/eval
- Dynamic weaving/registration systems

### 6.5 Floating Point and Machine-Level Numeric Semantics

(Pragmatic restriction: unless you standardize a formal float model, proofs tend to either mismatch runtime or require heavy infrastructure.)

**Rule V-FLOAT** (recommended default)
In Lean-checked code, either:

1. Forbid native Float arithmetic, or
2. Require a per-module float policy:
   - `float_model: real` — spec uses Real; runtime is refinement obligation, or
   - `float_model: axiomatic` — `@trusted` semantics, or
   - `float_model: ieee` — only if you ship a formal IEEE model.

---

## 7. AOP Constraints in Verification Mode

### 7.1 Verified Join Points

A verified join point is any join point targeting a Lean-checked function/method/constructor.

### 7.2 Core Rule: Only Ghost Aspects May Target Verified Join Points

**Rule V-AOP-GHOST** (mandatory)
If a pointcut matches any verified join point, the aspect must be `@ghost`. Otherwise: compile error.

This ensures weaving cannot change runtime semantics of verified code.

### 7.3 Pointcut Determinism (Recommended; Strongly Advised)

**Rule V-AOP-EXPLICIT** (recommended)
In Lean-checked contexts, pointcuts must be explicit symbol references (no wildcards, no package globs).

**Allowed:**

```simple
pointcut p = call BankAccount.withdraw(amount: Int)
```

**Rejected:**

```simple
pointcut p = call bank.*
pointcut p = call *.withdraw
```

### 7.4 Advice Restrictions for Ghost Aspects

**Rule V-AOP-ADVICE** (mandatory for milestone-1)
For `@ghost` aspects targeting verified join points:

- `before` / `after`: allowed, but must only read/write ghost state
- `around`: allowed only if:
  - It calls `proceed` exactly once, and
  - Returns `proceed`'s result unchanged, and
  - Does not throw/handle runtime errors

### 7.5 Aspect Introductions (Members/Fields) in Verified Mode

**Rule V-AOP-INTRO** (mandatory)
No aspect may introduce runtime members/fields/types into Lean-checked classes. Ghost-only introductions are allowed only if they are private and non-observable.

---

## 8. Macro Constraints in Verification Mode

Macros are treated as compile-time transformers that can introduce declarations. In verification mode, macros must not be able to silently expand the public/global surface of Lean-checked code.

### 8.1 Macro Introduction Contract (Mandatory)

Any macro capable of introducing declarations must declare an `introduces:` contract that fully enumerates what it may create.

Each introduced item includes:

- `kind:` — `class.fn` | `class.field` | `class.type` | `global.fn` | `global.type` | ...
- `visibility:` — `pub` | `internal` | `private`
- `phase:` — `ghost` | `runtime`
- `target scope:` — `enclosing.class` | `enclosing.module` | `global`
- Name/signature template

**Example:**

```simple
macro define_counter(NAME: Str)
  introduces:
    - private ghost class.fn "{NAME}Counter"(start: Int) -> Int
  body:
    ...
```

### 8.2 No Undeclared Introductions

**Rule M-INTRO-EXACT** (mandatory)
After expansion, the compiler computes the set of introduced symbols. If any introduced symbol is not declared in `introduces:`, compilation fails.

### 8.3 Verified Macro Policy

**Rule V-MACRO-NO-PUB** (mandatory)
In Lean-checked contexts (including descendants of verified classes), a macro expansion must not introduce any public members.

**Rule V-MACRO-NO-GLOBAL** (mandatory)
In Lean-checked contexts, a macro expansion must not introduce any global declarations (functions/types/constants/variables), regardless of visibility.

**Rule V-MACRO-GHOST-ONLY** (mandatory for milestone-1)
In Lean-checked contexts, macros may introduce only private ghost declarations (e.g., helper lemmas, ghost counters, ghost trace hooks). Any runtime introduction is a compile error.

### 8.4 Macro-Generated Aspects

**Rule V-MACRO-AOP** (mandatory)
Macros used in Lean-checked contexts may not generate aspects except `@ghost` aspects that satisfy §7 (and must still obey "no public/global introduction" rules).

### 8.5 Optional Escape Hatch (Explicitly Trusted)

If needed later:

`@trusted_macro` on a macro definition allows runtime introductions, but:

- Any Lean-checked code using it is downgraded unless the introduced surface is explicitly allowlisted by the target class/module (export list).

For milestone-1, omit this feature to keep soundness simple.

---

## 9. Compiler Pipeline (Lean Backend)

### 9.1 Stages

1. Parse Simple
2. Expand macros
3. Resolve AOP weaving (static, deterministic order)
4. Enforce verification constraints (this spec)
5. Emit Lean artifacts:
   - Type translations
   - Function translations
   - Invariants/contracts as Lean `Prop`
   - Theorem stubs (proof obligations)
6. Run Lean to validate proofs (and/or compile the `.lean` files)

### 9.2 Lean Mapping (Baseline)

| Simple Construct | Lean Construct |
|------------------|----------------|
| `class` | `structure` |
| `enum` | `inductive` |
| `(T \| E)` | `Sum T E` (or project-defined `Either`) |
| invariants | `def inv : T → Prop` |
| contracts | theorem statements |

### 9.3 Treatment of Ghost

Ghost state is erased from runtime compilation; Lean generation may:

- Omit ghost runtime constructs entirely, or
- Model them as proof-only structures (recommended: erased).

---

## 10. Diagnostics (Minimum Required Error Set)

| Error Code | Description |
|------------|-------------|
| `V-AOP-001` | Non-ghost aspect targets verified join point |
| `V-AOP-002` | Verified pointcut uses wildcard/glob (if §7.3 enforced) |
| `V-AOP-003` | Aspect introduces runtime member into verified class |
| `M-INTRO-001` | Macro introduced symbol not declared in `introduces:` |
| `V-MACRO-001` | Macro introduces pub member in verified context |
| `V-MACRO-002` | Macro introduces global symbol in verified context |
| `V-MACRO-003` | Macro introduces runtime symbol in verified context |
| `V-TERM-001` | Recursion without acceptable termination argument |
| `V-UNSAFE-001` | Unsafe primitive used in verified context |
| `V-DEP-001` | Verified code depends on non-verified code without `@trusted` boundary |
| `V-INHERIT-001` | Derived class attempts to opt out of verified context |

Each error must include:

- File/line
- Affected declaration
- Macro/aspect name (if applicable)
- At least one concrete introduced/target symbol

---

## 11. Examples

### 11.1 Allowed: Ghost Aspect on Verified Method

```simple
@verify
class Account:
  balance: Int
  invariant:
    balance >= 0

  fun withdraw(x: Int) -> (Account | Err):
    requires: x >= 0
    ...

@aspect @ghost
aspect TraceWithdraw:
  pointcut p = call Account.withdraw(x: Int)

  before p:
    ghost Trace.record("enter withdraw")

  after p:
    ghost Trace.record("exit withdraw")
```

### 11.2 Rejected: Runtime Aspect on Verified Method

```simple
@aspect
aspect Retry:
  pointcut p = call Account.withdraw(x: Int)
  around p:
    return retry3(() => proceed())
```

**Error:** `V-AOP-001`

### 11.3 Rejected: Macro Introduces Public Member in Verified Descendant

```simple
@verify
class Base: ...

class Child : Base:
  use make_getter("x")   # expands to pub fn get_x() -> Int
```

**Error:** `V-MACRO-001`

### 11.4 Rejected: Macro Introduces Global Helper

```simple
@verify
class A:
  use define_helpers()  # expands to global fn normalize(...)
```

**Error:** `V-MACRO-002`

### 11.5 Allowed: Macro Introduces Private Ghost Lemma Helper

```simple
@verify
class A:
  use prove_inv_helpers()

macro prove_inv_helpers()
  introduces:
    - private ghost class.fn "lemma_inv_1"() -> Unit
  body:
    ...
```

---

## 12. Rationale Notes (Lean-Specific)

- Lean's reference explicitly separates "unsafe" definitions and notes they may use features that break assumptions about Lean's equational theory (unsafe casts, pointer equality, refcount observation). This is why the verified subset bans those features in Lean-checked code.

- Lean's termination framework requires decreasing measures and can require explicit termination proofs/scripts; this is why verified recursion requires `decreases:` or structural termination.

- Lean's partial/general recursion pathway is implemented through an unsafe auxiliary definition and an opaque constant, which is inappropriate for "prove what you run" verification mode, hence the ban in verified code.

---

## 13. Self-Hosting: Simple-Based Lean Generation

### 13.1 Goals

The Lean code generation should be self-hosted in Simple language, enabling:

1. **Bootstrap**: Simple generates its own verification artifacts
2. **Parallel Development**: Simple implementation runs alongside Rust until replacement
3. **Interface Parity**: Simple API mirrors Rust types/functions for seamless transition

### 13.2 Module Structure

```
simple/std_lib/src/verification/
├── __init__.spl              # Module manifest
├── lean/                     # Lean code generation
│   ├── __init__.spl
│   ├── codegen.spl           # Main code generator
│   ├── types.spl             # Type translation (class → structure, enum → inductive)
│   ├── contracts.spl         # Contract → Prop/theorem translation
│   ├── expressions.spl       # Expression translation
│   └── emitter.spl           # Lean syntax emission
├── models/                   # Verification models (mirrors verification/)
│   ├── __init__.spl
│   ├── memory_capabilities.spl   # RefCapability, CapType, Reference
│   ├── memory_model_drf.spl      # SC-DRF model
│   ├── contracts.spl             # Contract checking semantics
│   ├── type_inference.spl        # Type inference model
│   ├── async_compile.spl         # Effect tracking
│   ├── gc_manual_borrow.spl      # GC safety
│   ├── nogc_compile.spl          # NoGC instructions
│   ├── module_resolution.spl     # Module path resolution
│   └── visibility_export.spl     # Visibility rules
└── proofs/                   # Proof obligation management
    ├── __init__.spl
    ├── obligations.spl       # Proof stub generation
    └── checker.spl           # Lean invocation wrapper
```

### 13.3 Interface Parity with Rust

Simple types and functions must mirror the Rust implementation for eventual replacement:

| Rust Type/Function | Simple Equivalent | Location |
|--------------------|-------------------|----------|
| `RefCapability` enum | `enum RefCapability` | `models/memory_capabilities.spl` |
| `CapType` struct | `class CapType` | `models/memory_capabilities.spl` |
| `Reference` struct | `class Reference` | `models/memory_capabilities.spl` |
| `RefEnv` struct | `class RefEnv` | `models/memory_capabilities.spl` |
| `canCreateRef()` | `fn can_create_ref()` | `models/memory_capabilities.spl` |
| `ContractExpr` enum | `enum ContractExpr` | `models/contracts.spl` |
| `FunctionContract` struct | `class FunctionContract` | `models/contracts.spl` |
| `checkPreconditions()` | `fn check_preconditions()` | `models/contracts.spl` |
| `LeanCodegen` struct | `class LeanCodegen` | `lean/codegen.spl` |
| `emit_structure()` | `fn emit_structure()` | `lean/types.spl` |
| `emit_inductive()` | `fn emit_inductive()` | `lean/types.spl` |
| `emit_theorem()` | `fn emit_theorem()` | `lean/contracts.spl` |

### 13.4 Regenerating Current Lean Files

The Simple implementation must be able to regenerate all existing Lean files:

```simple
import verification.lean.codegen as codegen
import verification.models.memory_capabilities as memcap

# Regenerate verification/memory_capabilities/src/MemoryCapabilities.lean
fn regenerate_memory_capabilities() -> String:
    gen = codegen.LeanCodegen.new()

    # Add type definitions
    gen.add_inductive(memcap.RefCapability)
    gen.add_structure(memcap.CapType)
    gen.add_structure(memcap.Reference)
    gen.add_structure(memcap.RefEnv)

    # Add functions
    gen.add_def("hasActiveRefs", memcap.has_active_refs)
    gen.add_def("canCreateRef", memcap.can_create_ref)
    gen.add_def("canConvert", memcap.can_convert)

    # Add theorems
    gen.add_theorem("exclusive_is_unique", memcap.exclusive_is_unique_spec)
    gen.add_theorem("capabilities_prevent_races", memcap.data_race_freedom_spec)

    return gen.emit()
```

### 13.5 Verification Test Suite

Simple tests validate Lean generation matches existing files:

```simple
# simple/std_lib/test/unit/verification/lean_regen_spec.spl

describe "Lean Regeneration":
    context "memory_capabilities":
        it "generates identical MemoryCapabilities.lean":
            generated = regenerate_memory_capabilities()
            expected = File.read("verification/memory_capabilities/src/MemoryCapabilities.lean")
            expect(generated).to_equal(expected)

    context "contracts":
        it "generates identical Contracts.lean":
            generated = regenerate_contracts()
            expected = File.read("verification/type_inference_compile/src/Contracts.lean")
            expect(generated).to_equal(expected)
```

### 13.6 Transition Strategy

**Phase A: Parallel Implementation**
- Simple implementation generates Lean alongside existing files
- CI validates Simple output matches Rust output
- Both implementations maintained

**Phase B: Feature Parity**
- All Lean generation features implemented in Simple
- All 10 verification modules regenerable from Simple
- Performance benchmarks pass

**Phase C: Rust Deprecation**
- Simple becomes primary Lean generator
- Rust codegen marked deprecated
- Rust code removed after transition period

---

## Related Documentation

- [AOP Specification](aop.md) — Full AOP syntax and semantics
- [Macro System](../spec/macro.md) — Macro syntax and contracts
- [Contracts](../spec/functions.md#contracts) — Contract clause syntax
- [Memory Model](../architecture/memory_model_implementation.md) — SC-DRF verification
- [Verification Directory](../../verification/) — Existing Lean proofs
