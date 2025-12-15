# Simple Language Features

## Summary Statistics

**Overall Progress:** 22% (47/212 features complete)

| Category | Total | Complete | In Progress | Planned |
|----------|-------|----------|-------------|---------|
| Core Language | 50 | 38 | 8 | 4 |
| Codegen | 5 | 2 | 1 | 2 |
| Extended | 21 | 1 | 0 | 20 |
| Testing | 4 | 2 | 1 | 1 |
| Advanced | 127 | 0 | 0 | 127 |
| Infrastructure | 5 | 4 | 1 | 0 |

**Completed features:** See [feature_done_1.md](feature_done_1.md)

---

## In Progress Features

### Infrastructure

| Component | Status | Notes |
|-----------|--------|-------|
| **Codegen** | 🔄 Hybrid | Cranelift + LLVM, Interpreter fallback |
| **Module System** | 🔄 In Progress | Parsing ✅, Resolution ✅, Dependency graph pending |

### Core Language

- **Type Inference (HM)** 🔄
- **Unique Pointers** (&T, RAII) 📋
- **Shared Pointers** (*T, refcounting) 📋

### Codegen Features (#99-103)

- **Body Block Outlining** 📋 (Feature #99 - unblocks actors/generators/futures)
- **Future Body Execution** 📋
- **Codegen Parity Completion** 🔄

---

## Planned Features

### Extended Features (#200-220)

- **Unit Types** 📋 (network, file system, string suffixes)
- **Networking APIs** 📋 (TCP, UDP, HTTP, FTP)

### Testing Features (Planned)

| Feature ID | Feature | Status | Description |
|------------|---------|--------|-------------|
| TEST-010 | `shared_examples` | 📋 | Reusable example groups |
| TEST-011 | `it_behaves_like` | 📋 | Include shared examples |
| TEST-012 | `let` memoization | 📋 | Memoized per-example state |

### Test Directory Structure

```
test/
  __init__.spl           # Default imports (std.*, std.spec.*)
  environment/
    bootstrap.spl        # Process-level setup
    fixtures/            # Test data
    helpers/             # Shared utilities
  unit/                  # Fast, isolated tests
  integration/           # Module boundary tests
  system/                # End-to-end tests
```

### Coverage Policies

| Level | Coverage Target | Metric |
|-------|-----------------|--------|
| Unit | Internal functions | Line/branch coverage |
| Integration | Public functions | Touch coverage 100% |
| System | Public types | Logic-containing types 100% |

### Mock Library (from `doc/spec/mock.md`)

| Feature ID | Feature | Status | Description |
|------------|---------|--------|-------------|
| MOCK-001 | `mock <Type>` | 📋 | Create mock implementing interface |
| MOCK-002 | `spy <Type>` | 📋 | Create spy wrapping real object |
| MOCK-003 | `.when(:method)` | 📋 | Configure method behavior |
| MOCK-004 | `.with(args)` | 📋 | Match specific arguments |
| MOCK-005 | `.returns(value)` | 📋 | Set return value |
| MOCK-006 | `.returnsOnce(value)` | 📋 | Return value once, then default |
| MOCK-007 | `.verify(:method)` | 📋 | Verify method was called |
| MOCK-008 | `.called()` | 📋 | Assert at least one call |
| MOCK-009 | `.calledTimes(n)` | 📋 | Assert exact call count |
| MOCK-010 | `.calledWith(args)` | 📋 | Assert specific arguments |
| MOCK-011 | `any()` matcher | 📋 | Match any argument |
| MOCK-012 | `gt(x)`, `lt(x)` | 📋 | Comparison matchers |

### Mock Example

```simple
test "Should notify when user created":
    let notifier = mock Notifier
    let repo = mock UserRepository

    repo.when(:save).with(any(User)).returns(User(id:1, name:"Bob"))
    notifier.when(:notify).returns()

    let service = UserService(repo, notifier)
    service.createUser("Bob")

    notifier.verify(:notify).called()
```

### CLI Integration (Planned)

| Feature ID | Feature | Status | Description |
|------------|---------|--------|-------------|
| CLI-001 | `simple test` command | 📋 | Unified test runner |
| CLI-002 | `--unit` flag | 📋 | Run unit tests |
| CLI-003 | `--integration` flag | 📋 | Run integration tests |
| CLI-004 | `--system` flag | 📋 | Run system tests |
| CLI-005 | `--tag <name>` | 📋 | Filter by tag |
| CLI-006 | `--fail-fast` | 📋 | Stop on first failure |
| CLI-007 | `--seed N` | 📋 | Deterministic shuffle |
| CLI-008 | JSON formatter | 📋 | Machine-readable output |
| CLI-009 | Doc formatter | 📋 | Nested describe output |

---

## Contract Features (from `doc/spec/invariant.md`)

### Core Contract Blocks

| Feature ID | Feature | Status | Description |
|------------|---------|--------|-------------|
| CTR-001 | `in:` preconditions | 📋 | Boolean expressions that must be true at function entry |
| CTR-002 | `out(ret):` postconditions | 📋 | Conditions on success return value |
| CTR-003 | `out_err(err):` error postconditions | 📋 | Conditions on error return value |
| CTR-004 | `invariant:` routine invariants | 📋 | Must hold at entry and all exits |
| CTR-005 | `old(expr)` snapshots | 📋 | Capture values at function entry for postconditions |

### Type and Class Invariants

| Feature ID | Feature | Status | Description |
|------------|---------|--------|-------------|
| CTR-010 | Type `invariant:` block | 📋 | Class/struct-level invariants |
| CTR-011 | Entry/exit invariant checking | 📋 | Check on public method boundaries |
| CTR-012 | Module boundary checking | 📋 | Check when values cross API boundaries |

### Refinement Types

| Feature ID | Feature | Status | Description |
|------------|---------|--------|-------------|
| CTR-020 | `where` clause | 📋 | Attach predicates to base types |
| CTR-021 | Subtype relationships | 📋 | `T where P` is subtype of `T` |
| CTR-022 | Compile-time proof | 📋 | Constant folding, range propagation |
| CTR-023 | Runtime fallback | 📋 | Insert checks when proof fails |

### Purity Constraints

| Feature ID | Feature | Status | Description |
|------------|---------|--------|-------------|
| CTR-030 | Pure expression enforcement | 📋 | Contract expressions must be pure |
| CTR-031 | `@pure` function annotation | 📋 | Mark functions callable in contracts |
| CTR-032 | Impure call detection | 📋 | Compile error for impure calls |

### Build Modes

| Feature ID | Feature | Status | Description |
|------------|---------|--------|-------------|
| CTR-040 | `--contracts=off` | 📋 | No checks emitted |
| CTR-041 | `--contracts=boundary` | 📋 | Checks for public/exported only |
| CTR-042 | `--contracts=on` | 📋 | All contract checks |
| CTR-043 | `--contracts=test` | 📋 | Rich diagnostics mode |

### Contract Violations

| Feature ID | Feature | Status | Description |
|------------|---------|--------|-------------|
| CTR-050 | `ContractViolation.Pre` | 📋 | Precondition failure |
| CTR-051 | `ContractViolation.Post` | 📋 | Postcondition failure |
| CTR-052 | `ContractViolation.ErrPost` | 📋 | Error postcondition failure |
| CTR-053 | `ContractViolation.InvariantEntry` | 📋 | Invariant failure at entry |
| CTR-054 | `ContractViolation.InvariantExit` | 📋 | Invariant failure at exit |

### Snapshot-Safe Types

| Feature ID | Feature | Status | Description |
|------------|---------|--------|-------------|
| CTR-060 | Primitive snapshot | 📋 | i64, bool, enums in old() |
| CTR-061 | Immutable struct snapshot | 📋 | Value structs in old() |
| CTR-062 | `@snapshot` annotation | 📋 | Custom snapshot semantics |

### Contract Examples

```simple
# Function with full contracts
fn div(a: i64, b: i64) -> (i64 | DivByZero):
    in:
        b != 0

    invariant:
        true

    if b == 0:
        return DivByZero(msg: "division by zero")

    return a / b

    out(ret):
        ret * b == a

    out_err(err):
        old(b) == 0

# Refinement type
type PosI64 = i64 where self > 0
type NonZero = i64 where self != 0

fn safe_div(a: i64, b: NonZero) -> i64:
    return a / b

# Class invariant
class Account:
    balance: i64

    invariant:
        balance >= 0

    fn withdraw(amount: i64) -> (i64 | Str):
        in:
            amount > 0
            amount <= balance

        balance -= amount
        return balance

        out(ret):
            ret == old(balance) - amount
```

---

## Formal Verification Roadmap (Planned)

### Contract Verification

| Feature ID | Description | Priority | Difficulty | Source |
|------------|-------------|----------|------------|--------|
| FV-100 | Contract precondition semantics (`in:`) | High | 3 | CTR-001 |
| FV-101 | Contract postcondition semantics (`out(ret):`) | High | 3 | CTR-002 |
| FV-102 | Error postcondition semantics (`out_err(err):`) | High | 3 | CTR-003 |
| FV-103 | Routine invariant preservation | Medium | 3 | CTR-004 |
| FV-104 | `old(expr)` snapshot correctness | Medium | 2 | CTR-005 |
| FV-105 | Type invariant preservation | Medium | 3 | CTR-010 |
| FV-106 | Refinement type soundness (`where` clause) | High | 4 | CTR-020 |
| FV-107 | Pure expression enforcement | Medium | 2 | CTR-030 |

### Testing Framework Verification

| Feature ID | Description | Priority | Difficulty | Source |
|------------|-------------|----------|------------|--------|
| FV-110 | Mock call verification semantics | Medium | 2 | MOCK-007 |
| FV-111 | Spy delegation correctness | Medium | 2 | MOCK-002 |
| FV-112 | BDD hook ordering (before_each/after_each) | Low | 2 | TEST-004,005 |
| FV-113 | BDD hook scope (before_all/after_all) | Low | 2 | TEST-006,007 |
| FV-114 | Matcher composition correctness | Low | 2 | TEST-008 |

---

## Advanced Features (#400-536)

- **Contract Blocks** 📋 (requires/ensures/invariant)
- **Capability-Based Imports** 📋 (effect tracking)
- **UI Framework** 📋 (.sui files, GUI/TUI renderers)
- **Web Framework** 📋 (controllers, views, SSR)
- **GPU Kernels** 📋 (#[gpu] attribute)

---

## Next Priorities

### Immediate (Sprint)
1. Complete Feature #99 (Body Block Outlining) - unblocks actors/generators/futures
2. Finish Module System dependency graph
3. Type Inference full AST integration

### Short Term (Month)
1. Memory pointer types (#25-28)
2. Trait dynamic dispatch (#15)
3. Union types (#37)

### Medium Term (Quarter)
1. Unit types (#200-209)
2. Networking APIs (#210-215)
3. Contract blocks (#400-405)

---

## Status Legend

- ✅ **COMPLETE** - Fully implemented and tested (see [feature_done_1.md](feature_done_1.md))
- 🔄 **IN PROGRESS** - Partially implemented
- 📋 **PLANNED** - Designed, not yet implemented
- 🔮 **FUTURE** - Long-term goal

## Related Documentation

- `feature_done_1.md`: Archived completed features
- `feature_index.md`: Categorized feature catalog
- `FEATURE_STATUS.md`: Comprehensive status tracking (212 features)
- `status/*.md`: Individual feature documentation (63 files)
- `codegen_status.md`: MIR instruction coverage, runtime FFI
- `architecture.md`: Design principles and dependency rules
- `CLAUDE.md`: Development guide for contributors
