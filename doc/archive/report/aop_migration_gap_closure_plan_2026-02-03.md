# AOP Migration Gap Closure Plan
**Date:** 2026-02-03
**Author:** Claude Code
**Status:** Draft Plan

## Executive Summary

**Current State:**
- ✅ Core AOP: 30/49 features migrated (61%)
- ✅ Production Ready: Yes (core weaving complete)
- ⚠️ Advanced Features: 19 features remaining in Rust only

**Goal:** Achieve 100% feature parity between Rust and Simple implementations

**Timeline:** 2-3 weeks for full migration

---

## Gap Analysis Summary

### Tier 1: High-Value Gaps (16 features, ~4 days)

| Component | Features | Effort | Priority | Impact |
|-----------|----------|--------|----------|--------|
| **Hybrid DI System** | 7 | 2-3 days | HIGH | Advanced DI scenarios |
| **Mocking System** | 6 | 1-2 days | HIGH | Test infrastructure |
| **Architecture Rules** | 3 | 4-8 hours | HIGH | Parser completion |

### Tier 2: Medium-Value Gaps (3 features, ~1 day)

| Component | Features | Effort | Priority | Impact |
|-----------|----------|--------|----------|--------|
| **Constructor Injection** | 3 | 1 day | MEDIUM | Parameter validation |

### Tier 3: Low-Value Gaps (0 features currently planned)

Deferred optimization features:
- Release profile DI freezing
- Validation hooks
- Proceed enforcement

---

## Detailed Migration Tasks

### Phase 1: Hybrid DI System (7 features, 2-3 days)

**Goal:** Migrate dependency injection resolution from Rust to Simple

**Current Status:**
- ✅ Rust: Complete (`di_injection.rs`, 244 lines)
- ❌ Simple: No implementation

**Files to Create/Modify:**
1. `src/compiler/di.spl` (new, ~300 lines)
2. `src/compiler/di_resolver.spl` (new, ~200 lines)
3. `test/system/features/aop/di_spec.spl` (new, ~150 lines)

**Tasks:**

#### Task 1.1: DI Data Structures (4 hours)
```simple
# src/compiler/di.spl

class DependencyGraph:
    """Type-safe dependency graph with cycle detection"""
    nodes: Dict<text, DiNode>
    edges: Dict<text, List<text>>

    me add_dependency(from: text, to: text):
        # Add edge
        # Run DFS cycle detection

    fn has_cycle() -> bool:
        # DFS-based cycle detection

class DiBindingRule:
    """Binding rule: bind T on pc{...}"""
    interface_type: text
    impl_type: text
    pointcut: PredicateExpr
    priority: i32

    fn matches(context: DiContext) -> bool:
        # Evaluate pointcut in DI context

class DiResolveError:
    """DI resolution errors"""
    kind: DiErrorKind  # Ambiguous | NotFound | Cycle
    interface: text
    candidates: List<text>
```

#### Task 1.2: SDN Config Parsing (4 hours)
```simple
# src/compiler/di_config.spl

fn parse_di_config(sdn: SdnValue) -> Result<DiConfig, text>:
    """Parse di: section from simple.sdn"""
    val bindings = []

    for binding in sdn["di"]["bindings"]:
        val rule = DiBindingRule(
            interface_type: binding["interface"],
            impl_type: binding["implementation"],
            pointcut: parse_predicate(binding["on"]),
            priority: binding.get("priority") ?? 0
        )
        bindings.push(rule)

    Ok(DiConfig(bindings: bindings))
```

#### Task 1.3: Binding Resolution (8 hours)
```simple
# src/compiler/di_resolver.spl

class DiResolver:
    """Resolve DI bindings with priority/specificity"""
    bindings: List<DiBindingRule>
    graph: DependencyGraph

    fn resolve(interface: text, context: DiContext) -> Result<text, DiResolveError>:
        # Find all matching bindings
        val matches = bindings.filter(\b: b.matches(context))

        if not matches.?:
            Err(DiResolveError(kind: NotFound, interface: interface))
        elif matches.len() > 1:
            # Apply priority/specificity resolution
            val best = select_binding(matches)
            if best.?:
                Ok(best.impl_type)
            else:
                Err(DiResolveError(kind: Ambiguous, candidates: matches.map(\m: m.impl_type)))
        else:
            Ok(matches[0].impl_type)

    fn select_binding(candidates: List<DiBindingRule>) -> DiBindingRule?:
        # Sort by priority (higher first)
        val sorted = candidates.sort_by(\a, b: b.priority - a.priority)

        # Check if top two have same priority
        if sorted.len() >= 2 and sorted[0].priority == sorted[1].priority:
            None  # Ambiguous
        else:
            Some(sorted[0])
```

#### Task 1.4: Injection Points (4 hours)
```simple
# Integration with predicate system

# Add @sys.inject annotation support
# Add per-parameter @inject support
# Generate DI resolution calls during lowering
```

#### Task 1.5: Tests (4 hours)
```simple
# test/system/features/aop/di_spec.spl

feature "Hybrid Dependency Injection":
    scenario "Basic interface binding":
        given:
            interface Logger
            class FileLogger implements Logger
            bind Logger on pc{execution(*)}
        when:
            val logger = inject<Logger>()
        then:
            logger is FileLogger

    scenario "Priority resolution":
        given:
            bind Logger -> FileLogger on pc{execution(*)} priority 10
            bind Logger -> ConsoleLogger on pc{execution(*)} priority 5
        when:
            val logger = inject<Logger>()
        then:
            logger is FileLogger  # Higher priority wins

    scenario "Ambiguous binding detection":
        given:
            bind Logger -> FileLogger on pc{execution(*)}
            bind Logger -> ConsoleLogger on pc{execution(*)}
        when:
            val logger = inject<Logger>()
        then:
            error "Ambiguous binding for Logger"

    scenario "Circular dependency detection":
        given:
            class A depends on B
            class B depends on A
        when:
            inject<A>()
        then:
            error "Circular dependency: A -> B -> A"
```

**Deliverables:**
- ✅ `src/compiler/di.spl` (300 lines)
- ✅ `src/compiler/di_resolver.spl` (200 lines)
- ✅ `src/compiler/di_config.spl` (100 lines)
- ✅ `test/system/features/aop/di_spec.spl` (150 lines)
- ✅ 7/7 DI features migrated

---

### Phase 2: Mocking System (6 features, 1-2 days)

**Goal:** Migrate AOP-based mocking from Rust to Simple

**Current Status:**
- ✅ Rust: Complete (`mock.rs`, 200+ lines)
- ❌ Simple: No implementation

**Files to Create/Modify:**
1. `src/compiler/mock.spl` (new, ~250 lines)
2. `test/system/features/aop/mock_spec.spl` (new, ~200 lines)

**Tasks:**

#### Task 2.1: Mock Data Structures (3 hours)
```simple
# src/compiler/mock.spl

class MockBinding:
    """Mock binding for testing"""
    target: PredicateExpr  # What to mock
    behavior: MockBehavior  # What to return
    profile: text  # test/dev/all

    fn is_valid(current_profile: text) -> bool:
        # Check if mock allowed in current profile

enum MockBehavior:
    ReturnValue(value: RuntimeValue)
    ThrowError(error: text)
    CallOriginal
    Custom(fn: fn() -> RuntimeValue)

class MockExpectation:
    """Expected method calls for verification"""
    method: text
    args: List<RuntimeValue>
    times: ExpectedCallCount

enum ExpectedCallCount:
    Exactly(n: i32)
    AtLeast(n: i32)
    AtMost(n: i32)
    Between(min: i32, max: i32)
```

#### Task 2.2: Mock Syntax Parsing (4 hours)
```simple
# Parse mock declarations
mock UserService.get_user(id: 42).returns(fake_user)
mock PaymentService.charge(*).throws("Payment failed")
mock Logger.log(*).call_original()

# Expect method syntax
expect(UserService.get_user).called().times(3)
expect(PaymentService.charge).not_called()
```

#### Task 2.3: Test Profile Enforcement (2 hours)
```simple
fn validate_mock_profile(binding: MockBinding, current_profile: text) -> Result<(), text>:
    """Ensure mocks only used in test profile"""

    if binding.profile == "test" and current_profile != "test":
        Err("Mock binding '{binding.target}' only allowed in test profile")
    else:
        Ok(())
```

#### Task 2.4: Predicate-Based Mock Binding (4 hours)
```simple
# Bind mocks via predicates
mock on pc{execution(UserService.get_user(*))}:
    returns(fake_user)

mock on pc{execution(*.charge(*)) & within(PaymentService)}:
    throws("Payment failed")
```

#### Task 2.5: Tests (3 hours)
```simple
# test/system/features/aop/mock_spec.spl

feature "AOP Mocking":
    scenario "Return value mock":
        given:
            mock UserService.get_user(id: 42).returns(fake_user)
        when:
            val user = UserService.get_user(42)
        then:
            user == fake_user

    scenario "Throw error mock":
        given:
            mock PaymentService.charge(*).throws("Failed")
        when:
            PaymentService.charge(100)
        then:
            error "Failed"

    scenario "Test-only enforcement":
        given:
            profile: release
            mock Logger.log(*).returns(())
        when:
            compile()
        then:
            error "Mock only allowed in test profile"

    scenario "Expectation verification":
        given:
            expect(UserService.get_user).called().times(3)
        when:
            UserService.get_user(1)
            UserService.get_user(2)
            UserService.get_user(3)
        then:
            verification passes

    scenario "Expectation failure":
        given:
            expect(Logger.log).not_called()
        when:
            Logger.log("test")
        then:
            error "Expected Logger.log not to be called"
```

**Deliverables:**
- ✅ `src/compiler/mock.spl` (250 lines)
- ✅ `test/system/features/aop/mock_spec.spl` (200 lines)
- ✅ 6/6 mocking features migrated

---

### Phase 3: Architecture Rules Syntax (3 features, 4-8 hours)

**Goal:** Complete architecture rules parser (selectors already exist)

**Current Status:**
- ✅ Simple: Selectors implemented (`arch_rules.spl`, 123 lines)
- ⚠️ Simple: No syntax parser for `forbid`/`allow`

**Files to Modify:**
1. `src/compiler/arch_rules.spl` (extend existing)
2. `src/compiler/parser.spl` (add syntax support)
3. `test/system/features/aop/aop_architecture_rules_spec.spl` (expand)

**Tasks:**

#### Task 3.1: Parser Extension (3 hours)
```simple
# src/compiler/parser.spl

fn parse_arch_rules_block() -> List<ArchRule>:
    """
    Parse:
        arch_rules:
            forbid pc{import(std.unsafe.*)}
            allow pc{import(std.io.*) & within(*.test.*)}
    """
    expect_keyword("arch_rules")
    expect(Token::Colon)

    val rules = []
    while not at_block_end():
        val action = parse_rule_action()  # forbid | allow
        expect_keyword("pc")
        val predicate = parse_predicate_island()

        rules.push(ArchRule(action: action, predicate: predicate))

    rules

fn parse_rule_action() -> RuleAction:
    if match_keyword("forbid"):
        RuleAction::Forbid
    elif match_keyword("allow"):
        RuleAction::Allow
    else:
        error("Expected 'forbid' or 'allow'")
```

#### Task 3.2: SDN Config Support (2 hours)
```simple
# src/compiler/arch_rules.spl (extend)

fn from_sdn(config: SdnValue) -> List<ArchRule>:
    """Parse arch_rules from simple.sdn"""
    val rules = []

    for rule_sdn in config["arch_rules"]:
        val action = match rule_sdn["action"]:
            "forbid": RuleAction::Forbid
            "allow": RuleAction::Allow

        val predicate = parse_predicate(rule_sdn["predicate"])
        rules.push(ArchRule(action: action, predicate: predicate))

    rules
```

#### Task 3.3: Expand Tests (2 hours)
```simple
# test/system/features/aop/aop_architecture_rules_spec.spl (expand)

feature "Architecture Rules Syntax":
    scenario "Forbid syntax":
        given:
            arch_rules:
                forbid pc{import(std.unsafe.*)}
        when:
            import std.unsafe.ptr
        then:
            error "Architecture rule violated: import(std.unsafe.*) is forbidden"

    scenario "Allow syntax":
        given:
            arch_rules:
                allow pc{import(std.io.*) & within(*.test.*)}
        when:
            # In test file
            import std.io.file
        then:
            no error

    scenario "SDN config":
        given:
            # simple.sdn
            arch_rules:
              - action: forbid
                predicate: "import(std.unsafe.*)"
              - action: allow
                predicate: "import(std.io.*) & within(*.test.*)"
        when:
            load_config()
        then:
            rules parsed correctly
```

**Deliverables:**
- ✅ Extended `src/compiler/arch_rules.spl` (+50 lines)
- ✅ Extended `src/compiler/parser.spl` (+30 lines)
- ✅ Expanded `test/system/features/aop/aop_architecture_rules_spec.spl` (+50 lines)
- ✅ 3/3 architecture rule syntax features migrated

---

### Phase 4: Constructor Injection Rules (3 features, 1 day)

**Goal:** Add parameter-level injection validation

**Current Status:**
- ❌ Rust: Partial implementation
- ❌ Simple: Not implemented

**Files to Create/Modify:**
1. `src/compiler/di_validator.spl` (new, ~150 lines)
2. `test/system/features/aop/di_validation_spec.spl` (new, ~100 lines)

**Tasks:**

#### Task 4.1: Validation Rules (4 hours)
```simple
# src/compiler/di_validator.spl

class DiValidator:
    """Validate DI injection rules"""

    fn validate_constructor(ctor: Constructor) -> Result<(), DiValidationError>:
        # Rule 1: All params injectable or none
        val injectable_params = ctor.params.filter(\p: p.has_inject_annotation())

        if injectable_params.len() > 0 and injectable_params.len() < ctor.params.len():
            Err(DiValidationError(
                kind: MixedInjection,
                message: "Constructor has both @inject and non-@inject params",
                params: ctor.params.map(\p: p.name)
            ))

        # Rule 2: No mixing @sys.inject with @inject
        if ctor.has_class_inject() and injectable_params.len() > 0:
            Err(DiValidationError(
                kind: MixedAnnotations,
                message: "Cannot mix @sys.inject and @inject"
            ))

        Ok(())
```

#### Task 4.2: Parameter Diagnostics (2 hours)
```simple
fn report_di_error(error: DiValidationError):
    """Generate detailed diagnostic for DI errors"""

    match error.kind:
        MixedInjection:
            print_error("""
                Constructor injection rules violated

                All parameters must be injectable or none:
                {error.params.map(\p: "  - {p}").join("\n")}

                Either:
                  1. Add @inject to all parameters
                  2. Remove @inject from all parameters
                  3. Use @sys.inject on the class
            """)

        MixedAnnotations:
            print_error("""
                Cannot mix @sys.inject and @inject annotations

                Choose one approach:
                  - Class-level: @sys.inject on class
                  - Parameter-level: @inject on each param
            """)
```

#### Task 4.3: Tests (2 hours)
```simple
# test/system/features/aop/di_validation_spec.spl

feature "Constructor Injection Validation":
    scenario "All-or-nothing rule":
        given:
            class Service:
                # Mixed injection - ERROR
                fn __init__(@inject db: Database, config: Config):
                    pass
        when:
            compile()
        then:
            error "Constructor has both @inject and non-@inject params"

    scenario "No mixing annotations":
        given:
            @sys.inject
            class Service:
                # Also has @inject - ERROR
                fn __init__(@inject db: Database):
                    pass
        when:
            compile()
        then:
            error "Cannot mix @sys.inject and @inject"

    scenario "Valid class-level injection":
        given:
            @sys.inject
            class Service:
                fn __init__(db: Database, cache: Cache):
                    pass
        when:
            compile()
        then:
            no error

    scenario "Valid param-level injection":
        given:
            class Service:
                fn __init__(@inject db: Database, @inject cache: Cache):
                    pass
        when:
            compile()
        then:
            no error
```

**Deliverables:**
- ✅ `src/compiler/di_validator.spl` (150 lines)
- ✅ `test/system/features/aop/di_validation_spec.spl` (100 lines)
- ✅ 3/3 constructor injection features migrated

---

## Implementation Schedule

### Week 1: DI + Mocking (High Priority)

| Day | Tasks | Deliverable |
|-----|-------|-------------|
| **Mon** | Phase 1.1-1.2: DI data structures + SDN parsing | DI foundation |
| **Tue** | Phase 1.3-1.4: Binding resolution + injection points | DI resolver working |
| **Wed** | Phase 1.5 + Phase 2.1-2.2: DI tests + mock structures | DI complete, mock started |
| **Thu** | Phase 2.3-2.5: Mock profile + binding + tests | Mocking complete |
| **Fri** | Testing + bug fixes | Week 1 complete |

**Milestone:** ✅ Hybrid DI + Mocking migrated (13/19 features)

### Week 2: Architecture Rules + Constructor Validation

| Day | Tasks | Deliverable |
|-----|-------|-------------|
| **Mon** | Phase 3.1-3.2: Arch rules parser + SDN support | Parser working |
| **Tue** | Phase 3.3 + Phase 4.1: Arch tests + DI validator | Rules complete, validation started |
| **Wed** | Phase 4.2-4.3: Diagnostics + validation tests | Constructor rules complete |
| **Thu** | Integration testing across all phases | All features integrated |
| **Fri** | Documentation + final testing | Migration complete |

**Milestone:** ✅ All 19 features migrated (100%)

### Week 3: Polish + Optimization (Optional)

| Day | Tasks | Deliverable |
|-----|-------|-------------|
| **Mon** | Release profile DI freezing | Tier 3 feature 1 |
| **Tue** | Validation hooks | Tier 3 feature 2 |
| **Wed** | Proceed enforcement | Tier 3 feature 3 |
| **Thu** | Performance benchmarks | Optimization complete |
| **Fri** | Final documentation | 100% complete + optimized |

---

## Success Criteria

### Functional Requirements

- ✅ All 19 pending features implemented in Simple
- ✅ Feature parity with Rust implementation
- ✅ All tests passing (0 failures)
- ✅ Documentation updated

### Quality Requirements

- ✅ Code coverage ≥ 80% for new code
- ✅ No compiler warnings
- ✅ All SSpec tests executable
- ✅ Performance within 10% of Rust version

### Documentation Requirements

- ✅ Feature specs for all new features
- ✅ API documentation complete
- ✅ Migration guide updated
- ✅ Examples added to guide

---

## Risk Assessment

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| **DI circular detection complexity** | High | Medium | Reuse Rust algorithm, add extra tests |
| **Mock runtime overhead** | Medium | Low | Profile early, optimize if needed |
| **Parser syntax conflicts** | Medium | Low | Follow existing predicate patterns |
| **Test framework dependencies** | High | Medium | Mock test framework if needed |
| **Performance regression** | Medium | Medium | Benchmark against Rust baseline |

---

## Dependencies

### Required Before Starting:
- ✅ Predicate system complete (`predicate.spl`, `predicate_parser.spl`)
- ✅ Core AOP complete (`aop.spl`)
- ✅ Architecture rules selectors (`arch_rules.spl`)

### Can Proceed In Parallel:
- ⚠️ Test framework maturation (can use Rust tests initially)
- ⚠️ BDD framework completion (SSpec tests can be marked `@pending`)

### Blockers:
None identified - all prerequisites complete

---

## Metrics & Tracking

### Current Metrics (Before):
```
Total Features:        49
Migrated:              30 (61%)
Rust-Only:             19 (39%)
Lines of Code (Rust):  2,600+
Lines of Code (Simple): 1,500+
Test Coverage:         34/34 passing (100%)
```

### Target Metrics (After):
```
Total Features:        49
Migrated:              49 (100%)
Rust-Only:             0 (0%)
Lines of Code (Rust):  2,600+ (maintained)
Lines of Code (Simple): 2,500+ (67% increase)
Test Coverage:         60+ tests passing (100%)
```

### Progress Tracking:

Update `doc/test/test_db.sdn` after each phase completion:

```sdn
aop_migration_progress:
  total_features: 49
  migrated: {count}
  rust_only: {count}
  completion_percentage: {pct}

  phases:
    - name: "Hybrid DI"
      features: 7
      status: {pending|in_progress|complete}
      completion_date: {date}

    - name: "Mocking"
      features: 6
      status: {pending|in_progress|complete}
      completion_date: {date}

    # ... etc
```

---

## Post-Migration Tasks

### Phase 1: Verification (1 day)
1. Run full test suite (Rust + Simple)
2. Compare performance benchmarks
3. Verify feature parity via checklist
4. Update feature database

### Phase 2: Documentation (1 day)
1. Update `doc/research/aop.md`
2. Add migration notes to changelog
3. Create user-facing guide
4. Update API documentation

### Phase 3: Cleanup (1 day)
1. Remove deprecated Rust code (if applicable)
2. Consolidate duplicated logic
3. Optimize hot paths
4. Final code review

---

## Next Steps

### Immediate Actions:
1. ✅ Review this plan with stakeholders
2. ✅ Get approval to proceed
3. ✅ Set up tracking in `doc/test/test_db.sdn`
4. ✅ Create feature branches (if using git/jj)
5. ✅ Begin Phase 1: Hybrid DI System

### Before Starting Development:
- [ ] Verify all prerequisites complete
- [ ] Set up test infrastructure
- [ ] Create stub files for all new modules
- [ ] Configure CI for incremental testing

---

## Appendix: File Manifest

### New Files to Create:

| File | Lines | Purpose |
|------|-------|---------|
| `src/compiler/di.spl` | 300 | DI data structures |
| `src/compiler/di_resolver.spl` | 200 | Binding resolution |
| `src/compiler/di_config.spl` | 100 | SDN config parsing |
| `src/compiler/di_validator.spl` | 150 | Constructor validation |
| `src/compiler/mock.spl` | 250 | Mocking system |
| `test/system/features/aop/di_spec.spl` | 150 | DI tests |
| `test/system/features/aop/mock_spec.spl` | 200 | Mock tests |
| `test/system/features/aop/di_validation_spec.spl` | 100 | Validation tests |
| **TOTAL** | **1,450** | **8 new files** |

### Files to Modify:

| File | Current | Added | Purpose |
|------|---------|-------|---------|
| `src/compiler/arch_rules.spl` | 123 | +50 | Parser extension |
| `src/compiler/parser.spl` | ~3000 | +30 | Syntax support |
| `test/system/features/aop/aop_architecture_rules_spec.spl` | ~200 | +50 | Expanded tests |
| **TOTAL** | **~3323** | **+130** | **3 modified files** |

### Final Code Metrics:

```
New Code:              1,450 lines (8 files)
Modified Code:         130 lines (3 files)
Total Implementation:  1,580 lines
Test Code:             450 lines
Documentation:         ~500 lines (guides/specs)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
TOTAL EFFORT:          ~2,530 lines
```

---

## Conclusion

This plan provides a clear, actionable roadmap to achieve 100% AOP feature parity between Rust and Simple implementations. The phased approach prioritizes high-value features while maintaining production stability throughout the migration process.

**Recommended Action:** Approve and begin Phase 1 (Hybrid DI System) immediately.
