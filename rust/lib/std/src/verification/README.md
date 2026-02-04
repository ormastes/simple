# Verification Module - Self-Hosted Lean Code Generation

Self-hosted Simple implementation for generating Lean 4 verification code.

## Overview

This module provides:
- **Verification Models**: Simple implementations mirroring Lean proofs in `verification/`
- **Lean Code Generation**: Generate Lean 4 syntax from Simple models
- **Proof Obligation Management**: Track and check proof obligations
- **Regeneration**: Regenerate all existing Lean files from Simple

## Module Structure

```
verification/
├── __init__.spl              # Module exports
├── regenerate.spl            # Main regeneration entry point
├── models/                   # Verification models (mirrors verification/*.lean)
│   ├── memory_capabilities   # RefCapability, CapType, Reference
│   ├── memory_model_drf      # SC-DRF memory model
│   ├── contracts             # Contract checking semantics
│   ├── type_inference        # Hindley-Milner type inference
│   ├── async_compile         # Effect tracking
│   ├── gc_manual_borrow      # GC safety model
│   ├── nogc_compile          # NoGC compilation mode
│   ├── module_resolution     # Module path resolution
│   └── visibility_export     # Visibility rules
├── lean/                     # Lean 4 code generation
│   ├── codegen              # LeanCodegen class
│   ├── types                # Type translation
│   ├── contracts            # Contract → theorem translation
│   ├── expressions          # Expression translation
│   └── emitter              # Low-level Lean syntax
└── proofs/                   # Proof obligation management
    ├── obligations          # ProofObligation tracking
    └── checker              # Lean invocation wrapper
```

## Quick Start

### Generate Lean Code for Memory Capabilities

```simple
import verification.lean.codegen as codegen
import verification.models.memory_capabilities as memcap

# Create code generator
gen = codegen.LeanCodegen.new("MemoryCapabilities")

# Add RefCapability enum
ref_cap = codegen.build_enum("RefCapability", [
    ("Shared", []),
    ("Exclusive", []),
    ("Isolated", [])
])
gen = gen.add_inductive(ref_cap)

# Add CapType structure
cap_type = codegen.build_class("CapType", [
    ("baseType", codegen.make_string_type()),
    ("capability", codegen.make_simple_type("RefCapability"))
])
gen = gen.add_structure(cap_type)

# Generate Lean code
lean_code = gen.emit()
print(lean_code)
```

Output:
```lean
inductive RefCapability where
  | Shared : RefCapability
  | Exclusive : RefCapability
  | Isolated : RefCapability
deriving DecidableEq, Repr

structure CapType where
  baseType : String
  capability : RefCapability
deriving Repr
```

### Regenerate All Lean Files

```simple
import verification.regenerate as regen

# Regenerate all verification files
files = regen.regenerate_all()

for (path, content) in files.items():
    print("Generated: " + path)
    print(content[:100] + "...")
```

### Work with Proof Obligations

```simple
import verification.proofs.obligations as ob
import verification.models.contracts as c

# Create contract
contract = c.FunctionContract.new()
contract = contract.with_precondition(
    c.ContractClause.new(
        c.ContractExpr.BinOpExpr("!=",
            c.ContractExpr.VarExpr("x"),
            c.ContractExpr.ValExpr(c.Val.IntVal(0))
        )
    )
)

# Extract obligations
obligations = ob.extract_from_contract(
    "divide",
    "math.spl",
    10,
    contract
)

# Track obligations
obligation_set = ob.ObligationSet.new("math")
for obl in obligations:
    obligation_set = obligation_set.add(obl)

print(obligation_set.summary())
```

## API Reference

### Lean Code Generation

#### `LeanCodegen`

Main code generator class.

```simple
class LeanCodegen:
    fn new(name: String) -> LeanCodegen
    fn add_structure(cls: ClassDef) -> LeanCodegen
    fn add_inductive(enum: EnumDef) -> LeanCodegen
    fn add_function(func: FunctionDef) -> LeanCodegen
    fn add_theorem(thm: LeanTheorem) -> LeanCodegen
    fn emit() -> String
```

#### Builder Functions

```simple
fn build_enum(name: String, variants: List[(String, List[(String, SimpleType)])]) -> EnumDef
fn build_class(name: String, fields: List[(String, SimpleType)]) -> ClassDef
fn build_function(name: String, params: List[(String, SimpleType)], ret: SimpleType, body: String) -> FunctionDef
fn build_theorem(name: String, params: List[(String, String)], prop: String, proof: String = "sorry") -> LeanTheorem
```

#### Type Constructors

```simple
fn make_int_type() -> SimpleType
fn make_bool_type() -> SimpleType
fn make_string_type() -> SimpleType
fn make_list_type(elem: SimpleType) -> SimpleType
fn make_option_type(inner: SimpleType) -> SimpleType
fn make_simple_type(name: String) -> SimpleType
```

### Verification Models

#### Memory Capabilities

```simple
enum RefCapability:
    Shared | Exclusive | Isolated

class CapType:
    base_type: String
    capability: RefCapability

class Reference:
    location: Int
    ref_type: CapType

class RefEnv:
    active_refs: List[(Int, List[Reference])]

fn can_create_ref(env: RefEnv, loc: Int, cap: RefCapability) -> Bool
fn can_convert(from: RefCapability, to: RefCapability) -> Bool
```

#### Contracts

```simple
enum Val:
    IntVal(n: Int) | BoolVal(b: Bool) | StrVal(s: String)
    | NilVal | ErrorVal(tag: String, payload: Val)

enum ContractExpr:
    ValExpr(v: Val) | VarExpr(name: String) | OldExpr(e: ContractExpr)
    | RetExpr | ErrExpr
    | BinOpExpr(op: String, left: ContractExpr, right: ContractExpr)

class FunctionContract:
    preconditions: List[ContractClause]
    invariants: List[ContractClause]
    postconditions: List[ContractClause]
    error_postconditions: List[ContractClause]
```

### Proof Obligations

#### `ProofObligation`

```simple
class ProofObligation:
    id: String
    name: String
    source_file: String
    source_line: Int
    proposition: String
    status: ProofStatus

    fn new(...) -> ProofObligation
    fn with_status(status: ProofStatus) -> ProofObligation
    fn with_proof(proof: String) -> ProofObligation
    fn to_lean_theorem() -> LeanTheorem
```

#### `ObligationSet`

```simple
class ObligationSet:
    module_name: String
    obligations: List[ProofObligation]

    fn new(module_name: String) -> ObligationSet
    fn add(obligation: ProofObligation) -> ObligationSet
    fn find_by_status(status: ProofStatus) -> List[ProofObligation]
    fn summary() -> String
```

#### `ProofChecker`

```simple
class ProofChecker:
    config: CheckerConfig

    fn new(config: CheckerConfig = CheckerConfig.new()) -> ProofChecker
    fn check_file(file_path: String) -> FileCheckResult
    fn check_obligations(obligations: ObligationSet) -> BatchCheckResult
```

## Examples

### Example 1: Generate Memory Capabilities Module

See `examples/memory_capabilities_gen.spl`:

```simple
import verification.regenerate as regen

lean_code = regen.regenerate_memory_capabilities()
File.write("output/MemoryCapabilities.lean", lean_code)
```

### Example 2: Custom Verification Model

```simple
import verification.lean.codegen as codegen

# Define custom state machine model
gen = codegen.LeanCodegen.new("StateMachine")

# State enum
state = codegen.build_enum("State", [
    ("Init", []),
    ("Running", [("data", codegen.make_int_type())]),
    ("Done", [])
])
gen = gen.add_inductive(state)

# Transition function
transition = codegen.build_function(
    "transition",
    [
        ("current", codegen.make_simple_type("State")),
        ("input", codegen.make_int_type())
    ],
    codegen.make_simple_type("State"),
    "match current with\n| Init => Running input\n| Running _ => Done\n| Done => Done"
)
gen = gen.add_function(transition)

# Safety theorem
safety = codegen.build_theorem(
    "no_transition_from_done",
    [("input", "Int")],
    "transition Done input = Done",
    "rfl"
)
gen = gen.add_theorem(safety)

print(gen.emit())
```

## Testing

Run verification module tests:

```bash
./target/debug/simple simple/std_lib/test/unit/verification/lean_regen_spec.spl
```

## Interface Parity with Rust

This Simple implementation mirrors the (planned) Rust Lean codegen interface:

| Rust (Planned) | Simple (Current) | Location |
|----------------|------------------|----------|
| `RefCapability` enum | `enum RefCapability` | `models/memory_capabilities.spl` |
| `LeanCodegen` struct | `class LeanCodegen` | `lean/codegen.spl` |
| `emit_structure()` | `fn emit_structure()` | `lean/types.spl` |
| `emit_theorem()` | `fn emit_theorem()` | `lean/contracts.spl` |

## Transition Plan

### Phase A: Parallel Implementation (Current)
- ✅ Simple models implemented
- ✅ Lean code generation working
- ✅ Can regenerate existing files
- ⏳ CI validation pending

### Phase B: Feature Parity
- ⏳ All 10 verification modules regenerable
- ⏳ Performance benchmarks
- ⏳ Full test coverage

### Phase C: Rust Deprecation
- ⏳ Simple becomes primary generator
- ⏳ Rust marked deprecated
- ⏳ Migration complete

## Contributing

When adding new verification models:

1. Create model in `models/` mirroring Lean structure
2. Add regeneration function in `regenerate.spl`
3. Add test in `test/unit/verification/`
4. Update this README

## Related Documentation

- [Lean Verification Specification](../../../doc/research/lean_verification_with_aop.md)
- [Implementation Plan](../../../doc/plans/lean_verification_implementation.md)
- [Existing Lean Proofs](../../../verification/)
- [Feature Documentation](../../../doc/features/feature.md)
