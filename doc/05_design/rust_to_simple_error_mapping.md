# Rust to Simple Error Code Mapping Analysis

**Date**: 2026-01-19
**Purpose**: Map Rust's ~500 error codes to Simple, identifying applicable errors and missing features
**Status**: Analysis Complete

---

## Executive Summary

Rust has **~500-600 error codes** (E0001-E0805+) covering a mature compiler with advanced features. Simple currently has **80 error codes**. This document analyzes each Rust error category and determines:

1. ✅ **Already Implemented** - Error exists in Simple
2. 📋 **Applicable - Add to Plan** - Simple needs this error
3. ❌ **Not Applicable** - Simple doesn't have this feature
4. 🔧 **Needs Feature** - Requires new language feature/subsystem

---

## Category-by-Category Analysis

### 1. PATTERN MATCHING & UNREACHABLE CODE (Rust E0001-E0050)

| Rust Code | Name | Simple Status | Action |
|-----------|------|---------------|--------|
| E0004 | Non-Exhaustive Pattern | ❌ Not Applicable | Simple doesn't have exhaustiveness checking yet |
| E0005 | Irrefutable Pattern | ❌ Not Applicable | Pattern matching exists but not this advanced |
| E0007 | Invalid Range Pattern | 📋 Add to Plan | **E0013**: Invalid range in pattern |
| E0008 | Invalid Literal Pattern | 📋 Add to Plan | **E0014**: Invalid literal in pattern |
| E0010 | Duplicate Binding | 📋 Add to Plan | **E1019**: Duplicate binding in pattern |

**Feature Gaps**:
- 🔧 **Exhaustiveness Checking** - Compile-time verification that all patterns covered
- 🔧 **Advanced Pattern Matching** - Guard clauses, nested patterns, destructuring

**Recommendation**: Add basic pattern errors (E0013-E0014), defer exhaustiveness to later phase.

---

### 2. FUNCTION & CALL ERRORS (Rust E0060-E0100)

| Rust Code | Name | Simple Status | Action |
|-----------|------|---------------|--------|
| E0061 | Wrong Argument Count | 📋 Add to Plan | **E1020**: Argument count mismatch `{expected}` vs `{found}` |
| E0062 | Wrong Argument Type | ✅ Exists | E1003 (Type Mismatch) |
| E0063 | Missing Struct Fields | 📋 Add to Plan | **E1021**: Missing required fields in struct literal |
| E0064 | Unknown Struct Field | ✅ Exists | E1007 (Missing Field) |
| E0069 | Return in Closure | 📋 Add to Plan | **E1104**: Return used in closure context |
| E0070 | Invalid Left-Hand Side | 📋 Add to Plan | **E1022**: Invalid left-hand side of assignment |
| E0071 | Invalid Struct Literal | 📋 Add to Plan | **E1023**: Invalid struct literal syntax |
| E0073 | Invalid Turbofish | ❌ Not Applicable | Simple doesn't use `::<>` syntax |
| E0080 | Const Eval Error | 📋 Add to Plan | **E1024**: Constant evaluation failed |

**Feature Gaps**: None - Simple has functions and structs

**Recommendation**: Add E1020-E1024 to compiler semantic errors.

---

### 3. TRAIT & IMPL ERRORS (Rust E0200-E0250)

| Rust Code | Name | Simple Status | Action |
|-----------|------|---------------|--------|
| E0200 | Unsafe Trait Impl | ❌ Not Applicable | Simple has no `unsafe` |
| E0201 | Duplicate Assoc Item | 📋 Add to Plan | **E1025**: Duplicate method in impl |
| E0204 | Unsafe Trait | ❌ Not Applicable | No `unsafe` |
| E0206 | Assoc Type Not in Trait | 📋 Add to Plan | **E1026**: Associated type not declared in trait |
| E0207 | Unconstrained Type Param | 📋 Add to Plan | **E1027**: Type parameter not constrained |
| E0210 | Orphan Rule Violation | ❌ Not Applicable | Simple may not have orphan rules |
| E0220 | Unknown Assoc Type | 📋 Add to Plan | **E1028**: Unknown associated type |
| E0225 | Multiple Trait Bounds | 📋 Add to Plan | **E1029**: Conflicting trait bounds |
| E0228 | Lifetime on Trait | 📋 Add to Plan | **E1030**: Invalid lifetime on trait |
| E0232 | Missing Impl Item | 📋 Add to Plan | **E1031**: Missing required trait method |

**Feature Gaps**:
- 🔧 **Trait System** (Partial) - Simple has traits but not all advanced features
- 🔧 **Associated Types** - Needs implementation
- 🔧 **Orphan Rules** - May or may not be applicable

**Recommendation**: Add E1025-E1031 for basic trait errors, evaluate orphan rules separately.

---

### 4. LIFETIME & SCOPE ERRORS (Rust E0300-E0350)

| Rust Code | Name | Simple Status | Action |
|-----------|------|---------------|--------|
| E0301 | Conflicting Borrow | ❌ Not Applicable | Simple uses GC, no explicit lifetimes |
| E0302 | Lifetime Too Short | ❌ Not Applicable | No explicit lifetimes |
| E0303 | Immutable Borrow Conflict | ❌ Not Applicable | GC-based |
| E0308 | Type Mismatch | ✅ Exists | E1003 |
| E0310 | Lifetime Bound Failed | ❌ Not Applicable | No lifetimes |
| E0312 | Region Mismatch | ❌ Not Applicable | No regions |
| E0315 | Outlives Requirement | ❌ Not Applicable | No lifetimes |

**Feature Gaps**:
- ❌ **Explicit Lifetimes** - Not applicable (Simple uses GC)
- ❌ **Borrow Checker** - Not applicable (GC-based memory model)
- 🔧 **Reference Capabilities** - Simple has `mut T`, `iso T`, but different semantics

**Recommendation**: Skip all lifetime errors. Add capability errors if needed (separate category).

---

### 5. OWNERSHIP & BORROW CHECKER (Rust E0382-E0510)

| Rust Code | Name | Simple Status | Action |
|-----------|------|---------------|--------|
| E0382 | Use After Move | ❌ Not Applicable | Simple uses GC, no moves |
| E0383 | Partial Move | ❌ Not Applicable | No moves |
| E0384 | Reassign Immutable | ✅ Exists | E1011 (Cannot assign to const) |
| E0499 | Multiple Mut Borrows | ❌ Not Applicable | GC-based |
| E0502 | Conflicting Borrows | ❌ Not Applicable | GC-based |
| E0505 | Move While Borrowed | ❌ Not Applicable | No explicit borrows |
| E0507 | Move Out of Borrowed | ❌ Not Applicable | No borrows |
| E0509 | Move Out of Drop | ❌ Not Applicable | GC handles cleanup |

**Feature Gaps**:
- ❌ **Ownership/Move Semantics** - Not applicable (GC-based)
- ❌ **Borrow Checker** - Not applicable
- 🔧 **Capability System** - Simple has `mut`/`iso`/`T` but different checking

**Recommendation**: Skip borrow checker errors entirely. Consider capability-specific errors:
- **E1301**: Capability violation (trying to mutate immutable)
- **E1302**: Isolation violation (aliasing isolated reference)

---

### 6. NAME RESOLUTION & SCOPE (Rust E0425-E0450)

| Rust Code | Name | Simple Status | Action |
|-----------|------|---------------|--------|
| E0425 | Unresolved Name | ✅ Exists | E1001 (Undefined variable) |
| E0426 | Undeclared Variable | ✅ Exists | E1001 |
| E0428 | Duplicate Definition | ✅ Exists | E1008 |
| E0429 | Self in Static | 📋 Add to Plan | **E1032**: `self` used in static context |
| E0430 | Self in Static Method | ✅ Covered | (Simple allows static methods) |
| E0431 | Self Import | 📋 Add to Plan | **E1033**: Invalid use of `self` in import |
| E0432 | Unresolved Import | 📋 Add to Plan | **E1034**: Import path not found |
| E0433 | Failed to Resolve | ✅ Exists | E1010 (Module not found) |
| E0434 | Invalid Self | 📋 Add to Plan | **E1035**: `self` in invalid context |
| E0435 | Closure Capture | 📋 Add to Plan | **E1036**: Cannot capture variable in closure |
| E0437 | Invalid Self Param | 📋 Add to Plan | **E1037**: Invalid `self` parameter type |
| E0446 | Private in Public | 📋 Add to Plan | **E1038**: Private type in public interface |
| E0449 | Invalid Visibility | 📋 Add to Plan | **E1039**: Visibility qualifier not allowed here |
| E0451 | Private Field | 📋 Add to Plan | **E1040**: Field is private |

**Feature Gaps**:
- 🔧 **Module System** (Partial) - Simple has modules, needs privacy checking
- 🔧 **Import System** - Needs better error handling
- 🔧 **Closure Capture Analysis** - Needs implementation

**Recommendation**: Add E1032-E1040 for module/visibility errors.

---

### 7. CASTING & TYPE CONVERSION (Rust E0600-E0610)

| Rust Code | Name | Simple Status | Action |
|-----------|------|---------------|--------|
| E0600 | Invalid Unary Op | 📋 Add to Plan | **E1041**: Cannot apply unary operator `{op}` to `{type}` |
| E0604 | Invalid Self Type | 📋 Add to Plan | **E1042**: `Self` type in invalid context |
| E0605 | Invalid Cast | ✅ Partial | E2007 (Failed to cast) |
| E0606 | Invalid Binary Op | ✅ Exists | E1005 (Invalid operation) |
| E0607 | Cannot Cast | ✅ Partial | E2007 |
| E0608 | Invalid Index Type | 📋 Add to Plan | **E1043**: Index must be integer, found `{type}` |
| E0609 | Invalid Field Access | ✅ Exists | E1012 (Undefined field) |
| E0610 | Invalid Tuple Index | 📋 Add to Plan | **E1044**: Tuple index out of range |

**Feature Gaps**: None - Simple has operators and casts

**Recommendation**: Add E1041-E1044 for operator/casting errors.

---

### 8. FIELD ACCESS & INDEXING (Rust E0599, E0614-E0630)

| Rust Code | Name | Simple Status | Action |
|-----------|------|---------------|--------|
| E0599 | No Method Named | ✅ Exists | E1013 (Unknown method) |
| E0614 | Invalid Field Assign | 📋 Add to Plan | **E1045**: Cannot assign to non-field expression |
| E0615 | Invalid Struct Field | ✅ Exists | E1007 (Missing field) |
| E0616 | Private Field | 📋 Add to Plan | **E1046**: Field `{field}` is private |
| E0617 | Cannot Borrow Mut | 📋 Add to Plan | **E1047**: Cannot borrow field as mutable |
| E0618 | Not Callable | 📋 Add to Plan | **E1048**: Type `{type}` is not callable |

**Feature Gaps**:
- 🔧 **Field Privacy** - Needs implementation
- 🔧 **Mutable Field Borrowing** - May need capability checking

**Recommendation**: Add E1045-E1048 for field/method access errors.

---

### 9. CLOSURE & FUNCTION TRAITS (Rust E0620-E0650)

| Rust Code | Name | Simple Status | Action |
|-----------|------|---------------|--------|
| E0620 | Invalid Call | 📋 Add to Plan | **E1049**: Cannot call non-function type |
| E0621 | Disallowed Coercion | 📋 Add to Plan | **E1050**: Type coercion not allowed here |
| E0623 | Lifetime in Closure | ❌ Not Applicable | No lifetimes |
| E0631 | Closure Type Mismatch | 📋 Add to Plan | **E1051**: Closure signature doesn't match expected |
| E0635 | Unknown Inline Asm | ❌ Not Applicable | Simple doesn't have inline asm |
| E0637 | & in let-else | 📋 Add to Plan | **E1052**: Reference not allowed in let-else pattern |

**Feature Gaps**:
- 🔧 **Lambda/Closure System** (Partial) - Simple has `\x: expr` but needs type checking
- 🔧 **Function Traits** - May need Fn/FnMut/FnOnce equivalent

**Recommendation**: Add E1049-E1052 for closure errors.

---

### 10. MUTABILITY & REFERENCES (Rust E0596-E0598)

| Rust Code | Name | Simple Status | Action |
|-----------|------|---------------|--------|
| E0596 | Cannot Borrow Immutable | 📋 Add to Plan | **E1053**: Cannot create mutable reference to immutable |
| E0597 | Borrowed Too Short | ❌ Not Applicable | GC-based |
| E0598 | Invalid Deref | 📋 Add to Plan | **E1054**: Cannot dereference type `{type}` |

**Feature Gaps**:
- 🔧 **Reference System** - Simple has different semantics (capabilities)

**Recommendation**: Add E1053-E1054 for mutability errors, skip lifetime errors.

---

### 11. GENERIC TYPE & CONST ERRORS (Rust E0697-E0750)

| Rust Code | Name | Description | Simple Status | Action |
|-----------|------|-------------|---------------|--------|
| E0697 | Const Generic Not Allowed | Const generics in unsupported context | ❌ Not Applicable | Simple doesn't have const generics yet |
| E0698 | Type Alias Bounds | Bounds on type alias | 📋 Add to Plan | **E1055**: Type alias cannot have bounds |
| E0700 | Break Outside Loop | `break` outside loop | ✅ Exists | E1101 |
| E0701 | Continue Outside Loop | `continue` outside loop | ✅ Exists | E1102 |
| E0704 | Return Outside Function | `return` at module level | ✅ Exists | E1103 |
| E0705 | Invalid Range | Invalid range expression | 📋 Add to Plan | **E1056**: Invalid range `{from}..{to}` |
| E0706 | Async in Trait | `async fn` in trait | ❌ Not Applicable | Simple async different |
| E0708 | Yield Outside Generator | `yield` outside generator | 📋 Add to Plan | **E1057**: `yield` outside generator function |
| E0712 | Thread Local Static | Thread-local restrictions | ❌ Not Applicable | Different threading model |
| E0714 | Invalid Doc Comment | Doc comment in wrong place | 📋 Add to Plan | **E1058**: Documentation comment in invalid location |
| E0716 | Temporary Borrow | Temporary dropped while borrowed | ❌ Not Applicable | GC-based |
| E0718 | `!` Type Mismatch | Never type coercion failed | ❌ Not Applicable | Simple may not have `!` type |
| E0720 | Invalid Opaque Type | Opaque type constraints | ❌ Not Applicable | Different generics system |
| E0722 | Return Position `impl Trait` | RPIT constraints | ❌ Not Applicable | Different generics |
| E0726 | Invalid Implicit Deref | Deref coercion failed | 📋 Add to Plan | **E1059**: Cannot implicitly dereference `{type}` |
| E0728 | GAT Mismatch | Generic associated type error | ❌ Not Applicable | No GATs yet |
| E0730 | Invalid Const | Invalid const expression | 📋 Add to Plan | **E1060**: Expression not valid in const context |
| E0731 | Variadic Function | Variadic fn restrictions | ❌ Not Applicable | Simple doesn't have variadics |
| E0732 | Empty Enum | Zero-variant enum | 📋 Add to Plan | **E1061**: Enum must have at least one variant |
| E0733 | Recursion Limit | Recursion limit exceeded | 📋 Add to Plan | **E1062**: Recursion limit exceeded during {phase} |
| E0734 | Stability Attribute | `#[stable]` misuse | ❌ Not Applicable | No stability system |
| E0735 | Type Overflow | Type too large | 📋 Add to Plan | **E1063**: Type size limit exceeded |
| E0740 | Union Field | Union restrictions | ❌ Not Applicable | No unions |
| E0744 | Control Flow | Invalid control flow | 📋 Add to Plan | **E1105**: Invalid control flow in {context} |
| E0745 | Intrinsic Type | Wrong intrinsic type | 📋 Add to Plan | **E1064**: Intrinsic function requires type `{expected}` |
| E0746 | Return Type | Return type error | 📋 Add to Plan | **E1065**: Function return type error |
| E0747 | Const Arg Mismatch | Const generic mismatch | ❌ Not Applicable | No const generics |
| E0748 | Non-Lifetime Binder | For<T> without lifetime | ❌ Not Applicable | Different generics |
| E0749 | Negative Impl | Negative impl restrictions | ❌ Not Applicable | No negative impls |
| E0750 | `box` Pattern | Box pattern restrictions | ❌ Not Applicable | Different ownership |

**Feature Gaps**:
- ❌ **Const Generics** - Not in Simple yet
- ❌ **Generic Associated Types (GATs)** - Not in Simple
- ❌ **Never Type (`!`)** - May not be applicable
- 🔧 **Generator/Yield** - Needs implementation
- 🔧 **Advanced Generics** - Partial support

**Recommendation**: Add E1055-E1065, E1105 for applicable errors. Skip const generics, GATs, never type.

---

### 12. ATTRIBUTES, MACROS & COMPILATION (Rust E0750-E0806)

| Rust Code | Name | Simple Status | Action |
|-----------|------|---------------|--------|
| E0751 | `main` Trait | `main` signature wrong | 📋 Add to Plan | **E1066**: Invalid `main` function signature |
| E0752 | Nested Extern | Invalid extern block nesting | ❌ Not Applicable | Different FFI |
| E0753 | Async Trait | `async` trait not allowed | ❌ Not Applicable | Different async |
| E0754 | Async Closure | `async` closure not stable | ❌ Not Applicable | Different async |
| E0755 | Built-in Attribute | Misuse of built-in attribute | 📋 Add to Plan | **E1067**: Invalid use of built-in attribute `{attr}` |
| E0756 | `repr(transparent)` | Invalid transparent repr | ❌ Not Applicable | Different repr system |
| E0758 | Keyword in Macro | Reserved keyword in macro | 📋 Add to Plan | **E1403**: Reserved keyword `{keyword}` in macro |
| E0760 | `or` Pattern Binding | Inconsistent bindings in or-pattern | 📋 Add to Plan | **E1068**: Inconsistent bindings in pattern alternatives |
| E0761 | Multiple Panic Handlers | Duplicate panic handlers | ❌ Not Applicable | Different panic system |
| E0762 | Mismatched Binding | Variable binding mismatch | 📋 Add to Plan | **E1069**: Mismatched variable bindings |
| E0763 | Incompatible FFI Type | Type not FFI-safe | 📋 Add to Plan | **E4005**: Type `{type}` is not FFI-safe |
| E0764 | Manually Dropped | ManuallyDrop restrictions | ❌ Not Applicable | GC-based |
| E0765 | `#[default]` Variant | Default variant errors | 📋 Add to Plan | **E1070**: Invalid use of `#[default]` on enum variant |
| E0766 | Attribute Position | Attribute in wrong place | 📋 Add to Plan | **E1071**: Attribute `{attr}` not allowed here |
| E0767 | `#[naked]` Function | Naked function restrictions | ❌ Not Applicable | No naked functions |
| E0768 | C-variadic in Foreign | C varargs restrictions | ❌ Not Applicable | Different FFI |
| E0769 | `impl Trait` in FFI | Opaque type in FFI | ❌ Not Applicable | Different FFI |
| E0770 | Destructuring Assignment | Invalid destructuring | 📋 Add to Plan | **E1072**: Invalid destructuring assignment |
| E0771 | Non-Exhaustive Type | `#[non_exhaustive]` errors | 📋 Add to Plan | **E1073**: Cannot construct non-exhaustive type |
| E0773 | Stability Feature | Feature stability errors | ❌ Not Applicable | No stability system |
| E0774 | `#[track_caller]` Misuse | Track caller errors | ❌ Not Applicable | Different introspection |
| E0775 | Unterminated Attribute | Attribute syntax error | 📋 Add to Plan | **E0015**: Unterminated attribute |
| E0777 | C-Unwind ABI | C-unwind restrictions | ❌ Not Applicable | Different FFI |
| E0778 | Conflicting `repr` | Multiple repr attributes | 📋 Add to Plan | **E1074**: Conflicting representation attributes |
| E0779 | `#[inherit]` Misuse | Inherit attribute error | ❌ Not Applicable | No inherit system |
| E0780 | Discriminant Overflow | Enum discriminant too large | 📋 Add to Plan | **E1075**: Enum discriminant overflow |
| E0781 | `#[rustc_on_unimplemented]` | Internal attribute misuse | ❌ Not Applicable | Internal compiler |
| E0782 | Trait Upcasting | Trait object upcasting error | ❌ Not Applicable | Different trait objects |
| E0783 | Auto Trait Impl | Auto trait restrictions | ❌ Not Applicable | No auto traits |
| E0784 | Lang Item Not Found | Missing lang item | ❌ Not Applicable | Internal compiler |
| E0785 | Multiple Lang Items | Duplicate lang items | ❌ Not Applicable | Internal compiler |
| E0786 | Intrinsic Not Found | Unknown intrinsic | 📋 Add to Plan | **E1076**: Unknown compiler intrinsic `{name}` |
| E0787 | Intrinsic Signature | Wrong intrinsic signature | 📋 Add to Plan | **E1077**: Intrinsic `{name}` has wrong signature |
| E0788 | `#[alloc_error_handler]` | Alloc error handler errors | ❌ Not Applicable | GC-based |
| E0789 | Invalid Intrinsic Return | Intrinsic return type error | 📋 Add to Plan | **E1078**: Intrinsic must return `{expected}` |
| E0790 | Missing Generic Args | Generic arguments missing | 📋 Add to Plan | **E1079**: Missing generic arguments for `{item}` |
| E0791 | Mixed Inline Asm | Mixed asm dialects | ❌ Not Applicable | No inline asm |
| E0792 | Expected Item | Expected item, found token | 📋 Add to Plan | **E0016**: Expected item, found `{found}` |
| E0793 | Packed Repr Misuse | `#[repr(packed)]` errors | ❌ Not Applicable | Different repr |
| E0794 | Cannot Capture | Capture in async block | ❌ Not Applicable | Different async |
| E0795 | Misplaced Asm | Asm in wrong context | ❌ Not Applicable | No inline asm |
| E0796 | Multiple Asm Options | Conflicting asm options | ❌ Not Applicable | No inline asm |
| E0797 | Invalid Asm Label | Invalid asm label | ❌ Not Applicable | No inline asm |
| E0798 | Invalid Asm Const | Invalid const in asm | ❌ Not Applicable | No inline asm |
| E0799 | Invalid Asm Sym | Invalid symbol in asm | ❌ Not Applicable | No inline asm |
| E0800 | `dyn*` Trait Error | Experimental dyn* errors | ❌ Not Applicable | Different trait objects |
| E0801 | Type Too Complex | Type complexity limit | 📋 Add to Plan | **E1080**: Type is too complex |
| E0802 | Generic Const Eval | Generic const evaluation error | ❌ Not Applicable | No const generics |
| E0803 | `#[diagnostic]` Attribute | Diagnostic attribute errors | ❌ Not Applicable | Internal compiler |
| E0804 | Invalid Stability Attr | Stability annotation error | ❌ Not Applicable | No stability system |
| E0805 | Invalid Unsafe Block | Unsafe block validation | ❌ Not Applicable | No unsafe |
| E0806 | Next Available | Placeholder | 📌 Reserved | For future use |

**Feature Gaps**:
- ❌ **`unsafe` System** - Not applicable to Simple
- ❌ **Inline Assembly** - Not in Simple
- ❌ **Advanced FFI** (C-unwind, repr, etc.) - Simpler FFI model
- ❌ **Stability Attributes** - Not needed
- ❌ **Lang Items** - Internal compiler concept
- 🔧 **Macro System** - Simple has macros, needs better error handling
- 🔧 **Attribute System** - Needs implementation

**Recommendation**: Add E0015-E0016 (parser), E1066-E1080 (compiler), E1403 (macros), E4005 (FFI).

---

## Summary Statistics

### Rust Error Codes: ~500-600 total

| Category | Rust Codes | Simple Status | Count |
|----------|-----------|---------------|-------|
| ✅ **Already Implemented** | Various | E0001-E3009 | 80 |
| 📋 **Add to Plan** | E0007-E0792 | E0013-E1080+ | ~80 |
| ❌ **Not Applicable** | E0301-E0805 | N/A | ~300 |
| 🔧 **Needs Feature** | E0697-E0750 | Future | ~40 |

### Breakdown by Applicability

| Status | Count | Percentage |
|--------|-------|------------|
| **Not Applicable** (lifetimes, borrow checker, unsafe, const generics, GATs, advanced features) | ~300 | 60% |
| **Already Implemented** (existing Simple errors) | 80 | 16% |
| **Add to Plan** (applicable, missing) | ~80 | 16% |
| **Needs Features** (requires new subsystems) | ~40 | 8% |

---

## New Error Codes Proposed for Simple

### Parser Errors (E0013-E0020)

| Code | Name | Description |
|------|------|-------------|
| E0013 | Invalid Range Pattern | Invalid range in pattern matching |
| E0014 | Invalid Literal Pattern | Invalid literal in pattern |
| E0015 | Unterminated Attribute | Attribute syntax not closed |
| E0016 | Expected Item | Expected item, found token |

### Compiler Semantic Errors (E1019-E1080)

| Code | Name | Description |
|------|------|-------------|
| E1019 | Duplicate Binding | Duplicate binding in pattern |
| E1020 | Argument Count Mismatch | Wrong number of arguments in call |
| E1021 | Missing Struct Fields | Required fields missing in struct literal |
| E1022 | Invalid LHS Assignment | Invalid left-hand side of assignment |
| E1023 | Invalid Struct Literal | Struct literal syntax error |
| E1024 | Const Eval Failed | Constant evaluation failed |
| E1025 | Duplicate Method | Duplicate method in impl block |
| E1026 | Unknown Assoc Type | Associated type not in trait |
| E1027 | Unconstrained Type Param | Type parameter not constrained |
| E1028 | Unknown Assoc Type | Unknown associated type name |
| E1029 | Conflicting Trait Bounds | Multiple conflicting trait bounds |
| E1030 | Invalid Lifetime on Trait | Lifetime parameter invalid on trait |
| E1031 | Missing Trait Method | Required trait method not implemented |
| E1032 | Self in Static | `self` used in static context |
| E1033 | Invalid Self Import | Invalid `self` in import path |
| E1034 | Unresolved Import | Import path not found |
| E1035 | Invalid Self Context | `self` in invalid context |
| E1036 | Closure Capture Failed | Cannot capture variable in closure |
| E1037 | Invalid Self Param | Invalid `self` parameter type |
| E1038 | Private in Public | Private type in public interface |
| E1039 | Invalid Visibility | Visibility qualifier not allowed |
| E1040 | Private Field Access | Field is private |
| E1041 | Invalid Unary Op | Cannot apply unary operator to type |
| E1042 | Invalid Self Type | `Self` type in invalid context |
| E1043 | Invalid Index Type | Index must be integer |
| E1044 | Tuple Index OOB | Tuple index out of range |
| E1045 | Invalid Field Assign | Cannot assign to non-field |
| E1046 | Private Field | Field is private |
| E1047 | Cannot Borrow Mut Field | Cannot borrow field as mutable |
| E1048 | Not Callable | Type is not callable |
| E1049 | Cannot Call Non-Function | Cannot call non-function type |
| E1050 | Disallowed Coercion | Type coercion not allowed |
| E1051 | Closure Signature Mismatch | Closure signature doesn't match |
| E1052 | Invalid Let-Else Pattern | Reference in let-else pattern |
| E1053 | Cannot Borrow Immutable | Cannot create mutable ref to immutable |
| E1054 | Invalid Deref | Cannot dereference type |
| E1055 | Type Alias Bounds | Type alias cannot have bounds |
| E1056 | Invalid Range | Invalid range expression |
| E1057 | Yield Outside Generator | `yield` outside generator |
| E1058 | Invalid Doc Comment | Doc comment in invalid location |
| E1059 | Invalid Implicit Deref | Cannot implicitly dereference |
| E1060 | Invalid Const Expression | Expression not valid in const |
| E1061 | Empty Enum | Enum must have variants |
| E1062 | Recursion Limit | Recursion limit exceeded |
| E1063 | Type Size Limit | Type size limit exceeded |
| E1064 | Wrong Intrinsic Type | Intrinsic requires different type |
| E1065 | Invalid Return Type | Function return type error |
| E1066 | Invalid Main Signature | Invalid `main` function signature |
| E1067 | Invalid Builtin Attr | Invalid use of built-in attribute |
| E1068 | Inconsistent Bindings | Inconsistent bindings in pattern |
| E1069 | Mismatched Binding | Variable binding mismatch |
| E1070 | Invalid Default Variant | Invalid `#[default]` on variant |
| E1071 | Invalid Attr Position | Attribute not allowed here |
| E1072 | Invalid Destructuring | Invalid destructuring assignment |
| E1073 | Non-Exhaustive Type | Cannot construct non-exhaustive type |
| E1074 | Conflicting Repr | Conflicting representation attributes |
| E1075 | Discriminant Overflow | Enum discriminant overflow |
| E1076 | Unknown Intrinsic | Unknown compiler intrinsic |
| E1077 | Wrong Intrinsic Signature | Intrinsic has wrong signature |
| E1078 | Invalid Intrinsic Return | Intrinsic return type wrong |
| E1079 | Missing Generic Args | Missing generic arguments |
| E1080 | Type Too Complex | Type complexity limit |

### Control Flow Errors (E1104-E1105)

| Code | Name | Description |
|------|------|-------------|
| E1104 | Return in Closure | `return` used in closure |
| E1105 | Invalid Control Flow | Invalid control flow in context |

### Capability Errors (E1301-E1302) - NEW

| Code | Name | Description |
|------|------|-------------|
| E1301 | Capability Violation | Trying to mutate immutable capability |
| E1302 | Isolation Violation | Aliasing isolated reference |

### Macro Errors (E1403)

| Code | Name | Description |
|------|------|-------------|
| E1403 | Keyword in Macro | Reserved keyword in macro |

### FFI Errors (E4005)

| Code | Name | Description |
|------|------|-------------|
| E4005 | Type Not FFI-Safe | Type is not FFI-safe |

**Total New Errors**: ~84 codes

---

## Features Needed for Missing Errors

### 1. Exhaustiveness Checking 🔧

**Needed For**: E0004, E0005
**Description**: Compile-time verification that pattern matching covers all cases
**Priority**: Medium
**Estimated Effort**: 2-3 weeks

**SSpec Test**:
```simple
# test/features/pattern_exhaustiveness.spl
Feature: Pattern Matching Exhaustiveness

Scenario: Non-exhaustive match detected
  Given enum Option<T> = Some(T) | None
  When I write:
    '''
    match opt:
      Some(x): print(x)
    '''
  Then I should see error E0004: "non-exhaustive pattern: `None` not covered"
```

### 2. Advanced Pattern Matching 🔧

**Needed For**: E0007, E0008, E0010, E0760
**Description**: Guard clauses, or-patterns, range patterns, nested destructuring
**Priority**: Medium
**Estimated Effort**: 2-4 weeks

**SSpec Test**:
```simple
# test/features/advanced_patterns.spl
Feature: Advanced Pattern Matching

Scenario: Or-patterns with inconsistent bindings
  When I write:
    '''
    match x:
      A(y) | B(z): print(y)  # Error: y not bound in B
    '''
  Then I should see error E1068: "inconsistent bindings in pattern alternatives"

Scenario: Range patterns
  When I write:
    '''
    match n:
      0..10: print("low")
      10..20: print("medium")
      _: print("high")
    '''
  Then it should compile successfully
```

### 3. Associated Types 🔧

**Needed For**: E0206, E0220, E1026, E1028
**Description**: Types associated with traits (like Rust's `type Item`)
**Priority**: High
**Estimated Effort**: 3-4 weeks

**SSpec Test**:
```simple
# test/features/associated_types.spl
Feature: Associated Types in Traits

Scenario: Associated type in trait
  Given I define:
    '''
    trait Iterator:
      type Item
      fn next(me) -> Option<Item>
    '''
  When I implement:
    '''
    impl Iterator for MyIter:
      type Item = i32
      fn next(me) -> Option<i32>:
        # ...
    '''
  Then it should compile successfully

Scenario: Missing associated type
  When I implement Iterator without defining Item
  Then I should see error E1026: "associated type `Item` not declared in trait"
```

### 4. Generators/Yield 🔧

**Needed For**: E0708, E1057
**Description**: Generator functions with `yield` keyword
**Priority**: Low
**Estimated Effort**: 4-6 weeks

**SSpec Test**:
```simple
# test/features/generators.spl
Feature: Generator Functions

Scenario: Valid generator
  When I define:
    '''
    gen fn count_to_ten():
      for i in 0..=10:
        yield i
    '''
  Then it should compile successfully

Scenario: Yield outside generator
  When I write:
    '''
    fn regular():
      yield 42  # Error
    '''
  Then I should see error E1057: "`yield` outside generator function"
```

### 5. Closure Capture Analysis 🔧

**Needed For**: E0435, E1036
**Description**: Analysis of which variables closures capture and how
**Priority**: Medium
**Estimated Effort**: 2-3 weeks

**SSpec Test**:
```simple
# test/features/closure_capture.spl
Feature: Closure Variable Capture

Scenario: Cannot capture mutable variable
  When I write:
    '''
    fn foo():
      var x = 0
      spawn_thread(\: x = 1)  # Error: can't capture mut across threads
    '''
  Then I should see error E1036: "cannot capture variable `x` in closure"

Scenario: Valid capture
  When I write:
    '''
    fn foo():
      val x = 0
      val f = \: print(x)
      f()
    '''
  Then it should compile successfully
```

### 6. Module Privacy System 🔧

**Needed For**: E0446, E0449, E0616, E1038-E1040, E1046
**Description**: Public/private visibility for modules, types, fields
**Priority**: High
**Estimated Effort**: 2-3 weeks

**SSpec Test**:
```simple
# test/features/visibility.spl
Feature: Module Privacy

Scenario: Private type in public interface
  When I write:
    '''
    struct Private:
      field: i32

    pub fn leak() -> Private:  # Error
      Private(42)
    '''
  Then I should see error E1038: "private type `Private` in public interface"

Scenario: Access private field
  When I write:
    '''
    mod other:
      struct Foo:
        field: i32

    fn test():
      val foo = other.Foo(42)
      print(foo.field)  # Error: field is private
    '''
  Then I should see error E1046: "field `field` is private"
```

### 7. Capability System Enhancements 🔧

**Needed For**: E1301, E1302
**Description**: Enforce `mut T`, `iso T` capability constraints
**Priority**: High (core language feature)
**Estimated Effort**: 4-6 weeks

**SSpec Test**:
```simple
# test/features/capabilities.spl
Feature: Reference Capabilities

Scenario: Capability violation
  When I write:
    '''
    fn foo(x: T):  # Immutable capability
      x.mutate()   # Error: requires mut T
    '''
  Then I should see error E1301: "capability violation: trying to mutate immutable"

Scenario: Isolation violation
  When I write:
    '''
    fn bar(x: iso T):
      val y = x  # Error: can't alias isolated reference
      use(x)
      use(y)
    '''
  Then I should see error E1302: "isolation violation: aliasing isolated reference"
```

### 8. Const Evaluation 🔧

**Needed For**: E1024, E1060
**Description**: Compile-time constant evaluation
**Priority**: Medium
**Estimated Effort**: 3-4 weeks

**SSpec Test**:
```simple
# test/features/const_evaluation.spl
Feature: Constant Evaluation

Scenario: Valid const expression
  When I define:
    '''
    const SIZE: i32 = 10 * 20
    const NAME: str = "Simple"
    '''
  Then it should compile successfully

Scenario: Invalid const expression
  When I write:
    '''
    const INVALID: i32 = read_file("data.txt")  # Error: not const
    '''
  Then I should see error E1060: "expression not valid in const context"
```

---

## Implementation Priority

### High Priority (Next 3-6 months)

1. **Module Privacy** (E1038-E1046) - Core language feature
2. **Capability Enhancements** (E1301-E1302) - Core memory model
3. **Associated Types** (E1026-E1028) - Trait system completion
4. **Basic Pattern Errors** (E0013-E0016, E1019) - Language completeness

### Medium Priority (6-12 months)

5. **Closure Capture Analysis** (E1036) - Language safety
6. **Advanced Patterns** (E1068, E1052) - Pattern matching completion
7. **Const Evaluation** (E1024, E1060) - Optimization foundation
8. **Exhaustiveness Checking** (E0004) - Pattern safety

### Low Priority (12+ months)

9. **Generators** (E1057) - Nice-to-have feature
10. **Advanced Attributes** (E1067-E1074) - Tooling/metadata

---

## Conclusion

**Rust has ~500-600 error codes**, but **~60% are not applicable** to Simple due to different design choices:
- No borrow checker (GC-based memory model)
- No explicit lifetimes
- No `unsafe` blocks
- No const generics (yet)
- Simpler FFI model

**Simple should add ~84 new error codes** covering:
- ✅ Pattern matching (4 codes)
- ✅ Function/call errors (14 codes)
- ✅ Trait/type system (12 codes)
- ✅ Name resolution/modules (9 codes)
- ✅ Operations/casting (8 codes)
- ✅ Fields/methods (6 codes)
- ✅ Closures (5 codes)
- ✅ Mutability/references (3 codes)
- ✅ Generics/control (12 codes)
- ✅ Attributes/macros (10 codes)
- ✅ Capabilities (2 codes - NEW)
- ✅ FFI (1 code)

**Total error codes after expansion**: 80 (current) + 84 (new) = **164 error codes**

This would cover ~32% of Rust's error space while maintaining Simple's design philosophy.

---

**Next Steps**:
1. ✅ Update implementation plan with new error codes
2. ✅ Create SSpec tests for new errors
3. ✅ Prioritize feature implementations
4. ✅ Begin systematic implementation
