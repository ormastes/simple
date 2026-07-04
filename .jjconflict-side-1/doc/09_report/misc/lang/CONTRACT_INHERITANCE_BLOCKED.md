# Contract Inheritance - Implementation Blocked

**Date:** 2025-12-23
**Phase:** Phase 3 of Advanced Contracts
**Status:** ⏸️ **BLOCKED** - Waiting for basic inheritance implementation

---

## Summary

Phase 3 (Contract Inheritance) cannot proceed because **class inheritance is not yet implemented** in the Simple language. The parser has a `parent: Option<String>` field in `ClassDef`, but the `extends` keyword is not recognized, and there's no HIR/MIR support for inheritance.

---

## Current Status

### What Works ✅
- ✅ Phase 1: Function Contracts (preconditions, postconditions, old(), invariants)
- ✅ Phase 2: Class Invariants (constructor checks, method checks)
- ✅ AST has `parent` field in `ClassDef` (infrastructure exists)

### What's Blocked ⏸️
- ⏸️ Phase 3.1: Precondition Weakening
- ⏸️ Phase 3.2: Postcondition Strengthening
- ⏸️ Phase 3.3: Invariant Preservation

---

## Blocker Details

### Issue: `extends` Keyword Not Implemented

**Test:**
```simple
class Animal:
    name: str

class Dog extends Animal:
    breed: str
```

**Result:**
```
error: compile failed: parse: Unexpected token: expected Colon, found Identifier("extends")
```

### Root Cause Analysis

1. **Parser Level:** The `extends` keyword is not in the lexer token list
2. **AST Level:** `ClassDef.parent` field exists but is never populated
3. **HIR Level:** No support for parent type resolution or field/method inheritance
4. **MIR Level:** No support for virtual method dispatch or vtable construction
5. **Type System:** No subtype relationship or Liskov Substitution Principle enforcement

---

## Prerequisites for Phase 3

To implement contract inheritance, we first need:

### 1. Basic Inheritance Implementation (~40-60 hours)

#### 1.1 Parser Changes (~8 hours)
**File:** `src/parser/src/token.rs`
- Add `Extends` token

**File:** `src/parser/src/lexer/identifiers.rs`
- Recognize "extends" keyword

**File:** `src/parser/src/types_def/mod.rs`
- Parse `class Name extends Parent:` syntax
- Populate `ClassDef.parent` field

#### 1.2 HIR Changes (~12 hours)
**File:** `src/compiler/src/hir/types.rs`
- Add parent type reference to HirType::Struct
- Create type hierarchy data structure

**File:** `src/compiler/src/hir/lower/module_lowering.rs`
- Resolve parent type during class registration
- Inherit fields from parent
- Inherit methods from parent (or mark as overrideable)

#### 1.3 MIR Changes (~16 hours)
**File:** `src/compiler/src/mir/types.rs`
- Virtual method table (vtable) support
- Method override detection

**File:** `src/compiler/src/mir/lower.rs`
- Virtual method call lowering
- Super method call support

#### 1.4 Type System (~8 hours)
**File:** `src/compiler/src/hir/type_registry.rs`
- Subtype relationship (`is_subtype_of()`)
- Liskov Substitution Principle validation

#### 1.5 Codegen (~8 hours)
**File:** `src/compiler/src/codegen/cranelift.rs`
- Vtable construction
- Virtual dispatch code generation

#### 1.6 Testing (~8 hours)
- Basic inheritance tests
- Method override tests
- Field inheritance tests
- Virtual dispatch tests

---

## Phase 3 Design (Once Inheritance Works)

### 3.1 Precondition Weakening

**Principle:** Child classes can require **less** than parent classes.

**Validation:** At compile time, ensure child preconditions are weaker than or equal to parent preconditions.

**Runtime:** Check `parent_precondition OR child_precondition`

**Example:**
```simple
class Vehicle:
    fn start(fuel_level: i64):
        in:
            fuel_level > 10  # Requires more than 10% fuel

class ElectricCar extends Vehicle:
    fn start(fuel_level: i64):
        in:
            fuel_level > 5  # Weaker requirement (OK)
```

**Implementation:**
- **File:** `src/compiler/src/trait_coherence.rs`
- Add `check_precondition_weakening()` function
- Verify logical implication: `child_pre => parent_pre`

### 3.2 Postcondition Strengthening

**Principle:** Child classes can promise **more** than parent classes.

**Validation:** At compile time, ensure child postconditions are stronger than or equal to parent postconditions.

**Runtime:** Check `parent_postcondition AND child_postcondition`

**Example:**
```simple
class Account:
    fn withdraw(amount: i64) -> bool:
        out(ret):
            ret == true or ret == false  # Weak guarantee

class SavingsAccount extends Account:
    fn withdraw(amount: i64) -> bool:
        out(ret):
            ret == true  # Stronger guarantee (OK)
            # Also implies parent postcondition
```

**Implementation:**
- **File:** `src/compiler/src/trait_coherence.rs`
- Add `check_postcondition_strengthening()` function
- Verify logical implication: `parent_post => child_post`

### 3.3 Invariant Preservation

**Principle:** Child classes must maintain **all** parent invariants **plus** their own.

**Runtime:** Check parent invariants **and** child invariants.

**Example:**
```simple
class Vehicle:
    speed: i64
    invariant:
        self.speed >= 0

class Car extends Vehicle:
    fuel: i64
    invariant:
        self.fuel >= 0
        self.fuel <= 100

    fn new(initial_fuel: i64) -> Car:
        # Should check:
        # - speed >= 0 (parent invariant)
        # - fuel >= 0 (child invariant)
        # - fuel <= 100 (child invariant)
        return Car(speed: 0, fuel: initial_fuel)
```

**Implementation:**
- **File:** `src/compiler/src/hir/lower/module_lowering.rs`
- Function `collect_class_invariants()` to gather all ancestor invariants
- Modify invariant injection to include parent invariants

---

## Alternative: Trait-Based Approach

Since Simple has **traits**, we could implement contract inheritance for **trait implementations** first, which is simpler:

### Why Traits First?

1. **Already Implemented:** Trait system exists and works
2. **Simpler Semantics:** No field inheritance, only method contracts
3. **Immediate Value:** Contract validation for trait impls is useful
4. **Stepping Stone:** Easier path to full class inheritance

### Trait Contract Inheritance Example

```simple
trait Drawable:
    fn draw(self):
        in:
            # Trait specifies weak precondition
            true
        out:
            # Trait specifies strong postcondition
            self.is_visible()

class Circle implements Drawable:
    fn draw(self):
        in:
            self.radius > 0  # Stronger precondition (ERROR!)
        out:
            self.is_visible()  # Same postcondition (OK)
```

**Implementation Path:**
1. Parse trait contracts (already works)
2. Validate impl contracts against trait contracts
3. Ensure precondition weakening rule
4. Ensure postcondition strengthening rule

**Estimated Time:** ~12-16 hours (much simpler than class inheritance)

---

## Recommendation

Given the current state, I recommend:

### Option A: Trait Contract Validation (12-16 hours)
**Pros:**
- ✅ No new language features required
- ✅ Immediate practical value
- ✅ Simpler implementation
- ✅ Foundation for class inheritance later

**Cons:**
- ⚠️ Limited to trait implementations
- ⚠️ No field invariants

### Option B: Wait for Full Inheritance (~60 hours total)
**Pros:**
- ✅ Complete solution
- ✅ Class invariants work properly
- ✅ Full LSP support

**Cons:**
- ⚠️ Much larger time investment
- ⚠️ Blocked on other work
- ⚠️ More complex implementation

### Option C: Move to Phase 4 (Advanced Features)
**Pros:**
- ✅ No blockers
- ✅ Immediate user value
- ✅ Contract modes, diagnostics, etc.

**Cons:**
- ⚠️ Phase 3 remains incomplete
- ⚠️ Missing important LSP support

---

## Phase 4 Alternative: Advanced Features

If we skip Phase 3 for now, Phase 4 offers valuable enhancements:

### 4.1 Contract Modes CLI Integration (~8-10 hours)
- Implement `--contracts off|boundary|all|test` flag
- Thread ContractMode through compilation pipeline
- Conditional contract emission in MIR lowering

### 4.2 Custom Messages (~4-6 hours)
- Enhanced error messages with source context
- Already partially supported in AST

### 4.3 Rich Diagnostics (~12-16 hours)
- Source location tracking in ContractCheck
- Expression text capture
- Variable value snapshots (test mode)
- Stack traces for violations

### 4.4 Interpreter Integration (~8-10 hours)
- Complete the interpreter_contract.rs integration
- Add contract checking to function calls
- Wire up old() capture in interpreter

---

## Decision Points

**Question 1:** Should we implement trait contract validation first?
- This provides immediate value without waiting for inheritance

**Question 2:** Should we proceed with Phase 4 instead?
- Contract modes and diagnostics are highly useful

**Question 3:** Should we implement basic inheritance first?
- This unblocks Phase 3 but is a ~60 hour effort

---

## Current Recommendation: Option A (Trait Contracts)

Implement **trait contract validation** as "Phase 3 Light":

### Benefits
1. Validates contract compatibility for trait implementations
2. No dependency on class inheritance
3. Provides Liskov Substitution for interfaces
4. Foundation for future class inheritance
5. Estimated 12-16 hours

### Implementation Plan
1. **Parse trait contracts** - Already works ✅
2. **Validate impl contracts** - New feature (~6 hours)
3. **Precondition weakening check** - New feature (~3 hours)
4. **Postcondition strengthening check** - New feature (~3 hours)
5. **Testing** - Comprehensive tests (~2-4 hours)

---

## Conclusion

Phase 3 (Contract Inheritance for Classes) is **blocked** pending full inheritance implementation (~60 hours).

**Recommended Path Forward:**
1. ✅ Complete Phases 1-2 (DONE)
2. 🔄 Implement Trait Contract Validation (~12-16 hours) - "Phase 3 Light"
3. 🔄 Implement Phase 4 features (contract modes, diagnostics, etc.)
4. ⏭️ Return to full Phase 3 once inheritance is implemented

This approach provides continuous value delivery while avoiding blockers.

---

**Status:** ⏸️ Blocked (class inheritance not implemented)
**Alternative:** ✅ Trait contract validation available
**Next Step:** Decide between Option A (traits), B (wait), or C (Phase 4)

---

## Related Documentation

- [ADVANCED_CONTRACTS_COMPLETE.md](ADVANCED_CONTRACTS_COMPLETE.md) - Phase 1 completion
- [CLASS_INVARIANTS_COMPLETE.md](CLASS_INVARIANTS_COMPLETE.md) - Phase 2 completion
- [CONTRACTS_PHASE_1_AND_2_SUMMARY.md](CONTRACTS_PHASE_1_AND_2_SUMMARY.md) - Combined summary
