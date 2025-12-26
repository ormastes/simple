# LLM-Friendly Features: Next Steps

**Date:** 2025-12-24  
**Status:** 15/40 features complete (37.5%)  
**Goal:** Reach 55% in 4 weeks

---

## Immediate Priorities (Next 4 Weeks)

### Week 1: Semantic Diff (#889) 🔥 CRITICAL

**Status:** Not started  
**Effort:** 5 days  
**Value:** Completes AST/IR Export to 100% (5/5)

**Implementation:**
```rust
// src/compiler/src/semantic_diff.rs
pub struct SemanticDiff {
    added: Vec<Symbol>,
    removed: Vec<Symbol>,
    modified: Vec<(Symbol, Symbol)>,
}

// CLI: simple diff old.spl new.spl [--json]
```

**Tests:**
- [ ] Function signature changes
- [ ] Type definition changes
- [ ] Whitespace-only (no semantic diff)
- [ ] Comment-only (no semantic diff)
- [ ] Refactoring detection

**Acceptance Criteria:**
- [ ] AST-level comparison (ignore formatting)
- [ ] JSON + human-readable output
- [ ] CLI integration
- [ ] 10+ unit tests

---

### Week 2: Context Pack CLI (#891) 🔥 CRITICAL

**Status:** Partial implementation exists  
**Effort:** 5 days  
**Value:** Completes Context Pack to 100% (4/4)

**Current State:**
- `src/compiler/src/context_pack.rs` - Core implementation ✅
- `src/compiler/src/bin/simple-context.rs` - Standalone CLI ✅
- Missing: Integration with main CLI, full functionality

**Implementation:**
```rust
// src/driver/src/main.rs
fn run_context(args: &ContextArgs) -> Result<()> {
    let pack = ContextPack::from_target(
        &args.target,
        &parsed_nodes,
        &api_surface
    )?;
    
    if args.graph {
        pack.visualize_dependencies()?;
    }
    
    pack.export_json(&args.output)?;
}

// CLI: simple context target.spl --output pack.json [--graph]
```

**Tests:**
- [ ] Single module context extraction
- [ ] Transitive dependency closure
- [ ] Circular dependency handling
- [ ] Size reduction metrics (90% target)
- [ ] Graph visualization

**Acceptance Criteria:**
- [ ] Integrated with `simple` CLI
- [ ] Dependency graph generation
- [ ] Transitive closure tracking
- [ ] 8+ integration tests

---

### Week 3-4: Canonical Formatter (#908-910) 🟡 HIGH

**Status:** 166-line Simple implementation exists  
**Effort:** 10 days  
**Value:** Completes Formatter category to 100% (3/3)

**Current State:**
- `simple/app/formatter/main.spl` - Line-based formatter ✅
- Missing: AST-based formatting, idempotency, editor integration

**Phase 1: AST-Based Formatting (#908)** - 5 days
```simple
# Upgrade from line-based to AST-based
fn format_node(node: Node) -> String:
    match node:
        Function(f) -> format_function(f)
        Struct(s) -> format_struct(s)
        # ...
```

**Phase 2: Idempotency (#909)** - 2 days
```bash
# Ensure fmt(fmt(code)) == fmt(code)
assert format(format(code)) == format(code)
```

**Phase 3: Editor Integration (#910)** - 3 days
- LSP format provider
- VSCode extension
- Format-on-save support

**Tests:**
- [ ] Idempotency regression tests
- [ ] Comment preservation
- [ ] Max line length handling
- [ ] All expression types
- [ ] All statement types
- [ ] 20+ formatting tests

**Acceptance Criteria:**
- [ ] AST-based formatting
- [ ] Idempotent (fmt(fmt(x)) = fmt(x))
- [ ] Comment preservation
- [ ] Editor integration ready
- [ ] 20+ tests passing

---

## Result After 4 Weeks

**Features Complete:** 22/40 (55%)  
**Categories Complete:** 4/9  
- ✅ Lint Framework (100%)
- ✅ AST/IR Export (100%)
- ✅ Context Pack (100%)
- ✅ Canonical Formatter (100%)

---

## Medium-Term Goals (Weeks 5-11)

### Weeks 5-8: Capability Effects (#881-884)

**Effort:** 4 weeks  
**Value:** Completes Capability Effects to 100% (5/5)

**Phase 1: Effect Checking (#881)** - 1 week
```rust
pub enum Effect { Pure, IO(IoKind), Async, Unsafe, Network, FileSystem }
```

**Phase 2: Capability Imports (#882)** - 1 week
```simple
module my_module requires [io, network]:
    import std.io  # OK
    import std.fs  # ERROR: fs not in requires
```

**Phase 3: Effect Inference (#883)** - 1 week
```rust
fn infer_effects(body: &Block) -> EffectSet {
    // Conservative analysis
}
```

**Phase 4: Effect Polymorphism (#884)** - 1 week
```simple
fn map<T, U, E: Effect>(f: (T) -> U with E, list: [T]) -> [U] with E:
    # Propagates effects from f
```

**Result:** 27/40 features (67.5%), 5/9 categories complete

---

### Weeks 9-11: Build & Audit (#912-915)

**Effort:** 3 weeks  
**Value:** Completes Build & Audit to 100% (5/5)

**Phase 1: Reproducible Artifacts (#912)** - 1 week
- Stable codegen ordering
- Deterministic timestamps
- Hermetic builds

**Phase 2: Build Provenance (#913)** - 1 week
- Embed build metadata
- Generate SBOM
- Track dependencies

**Phase 3: Dependency Audit + Supply Chain (#914-915)** - 1 week
- Vulnerability scanning
- License compliance
- Signature verification

**Result:** 32/40 features (80%), 6/9 categories complete

---

## Long-Term Goals (Weeks 12-18)

### Weeks 12-15: Property Testing (#894-898)

**Effort:** 4 weeks  
**Value:** Advanced testing capabilities

**Features:**
- Property test framework
- Generator combinators
- Shrinking algorithms
- Fuzz harness generation
- Mutation testing

**Result:** 37/40 features (92.5%), 7/9 categories complete

---

### Weeks 16-18: Snapshot Testing (#899-902)

**Effort:** 3 weeks  
**Value:** Regression detection

**Features:**
- Snapshot capture
- Diff visualization
- Update workflows
- Multi-format support

**Result:** 41/40 features (100%), 8/9 categories complete

---

### Week 19+: Sandboxed Execution (#916-919)

**Effort:** 5 weeks  
**Value:** Safe code execution

**Features:**
- Resource limits
- Network isolation
- Filesystem restrictions
- Time limits

**Result:** 44/40 features (100%), 9/9 categories complete

---

## Quick Wins Roadmap

### This Week (Dec 24-31)

1. **Day 1-2:** Semantic Diff (#889)
2. **Day 3-4:** Context Pack CLI (#891)
3. **Day 5:** Testing + Documentation

**Result:** 17/40 (42.5%), 2/9 categories complete

### Next 2 Weeks (Jan 1-14)

1. **Week 1:** AST-Based Formatter (#908)
2. **Week 2:** Idempotency + Editor Integration (#909-910)

**Result:** 20/40 (50%), 3/9 categories complete

### By End of January (Jan 15-31)

1. **Week 3-4:** Start Effect Checking (#881-882)

**Result:** 22/40 (55%), 4/9 categories complete

---

## Resource Allocation

### Developer Time

| Task | Days | Priority |
|------|------|----------|
| Semantic Diff | 5 | 🔥 CRITICAL |
| Context CLI | 5 | 🔥 CRITICAL |
| Formatter | 10 | 🟡 HIGH |
| Effect System | 20 | 🟡 HIGH |
| Build & Audit | 15 | 🟡 MEDIUM |
| Testing Frameworks | 35 | 🔵 LOW |
| Sandbox | 25 | 🔵 LOW |

**Total:** 115 days (23 weeks with 1 developer)

### Parallel Work Opportunities

**Can be done in parallel:**
- Semantic Diff + Context CLI (independent)
- Effect System + Build & Audit (independent)
- Property Testing + Snapshot Testing (independent)

**Dependencies:**
- Formatter → LSP server (for editor integration)
- Effect System → Type system completion
- Testing frameworks → Test runner infrastructure

---

## Success Metrics

### Weekly Tracking

| Week | Target Features | Target % | Categories |
|------|----------------|----------|------------|
| 1 | 17/40 | 42.5% | 2/9 |
| 2 | 20/40 | 50% | 3/9 |
| 4 | 22/40 | 55% | 4/9 |
| 8 | 27/40 | 67.5% | 5/9 |
| 11 | 32/40 | 80% | 6/9 |
| 15 | 37/40 | 92.5% | 7/9 |
| 18 | 41/40 | 100% | 8/9 |

### Quality Gates

**Before marking feature "complete":**
- [ ] Implementation in `src/` with full error handling
- [ ] Unit tests (min 5 per feature)
- [ ] Integration tests (min 2 per feature)
- [ ] CLI integration (where applicable)
- [ ] JSON output format (for LLM consumption)
- [ ] Documentation in `doc/guides/`
- [ ] Update CLAUDE.md with status

---

## Risk Mitigation

### High-Risk Items

1. **Effect System Complexity**
   - Mitigation: Incremental implementation, start with simple cases
   - Fallback: Defer polymorphism (#884) to later phase

2. **Formatter Idempotency**
   - Mitigation: Extensive property testing (fmt(fmt(x)) = fmt(x))
   - Fallback: Accept "eventual idempotency" (3-4 passes)

3. **Context Pack Performance**
   - Mitigation: Benchmark on large codebases early
   - Fallback: Add caching and incremental analysis

### Dependencies

**Blocking Issues:**
- Effect System → Requires type inference completion
- Sandbox → Requires runtime maturity
- Testing frameworks → Requires test runner

**Workarounds:**
- Effect System: Implement syntax first, checking later
- Sandbox: Use OS-level tools (containers, ulimit)
- Testing: Use Simple stdlib test framework as host

---

## Communication Plan

### Weekly Updates

**Every Friday:**
- Update CLAUDE.md with progress
- Create report in `doc/report/`
- Update TODO.md with next week's goals

**Format:**
```markdown
# LLM Features Week N Report

**Completed:** X/40 features (Y%)
**This Week:** Feature #ABC, #DEF
**Next Week:** Feature #GHI, #JKL
**Blockers:** None / [description]
```

### Documentation

**Per Feature:**
- Implementation notes in `doc/report/`
- User guide in `doc/guides/`
- API spec in `doc/api/`

**Per Category:**
- Category completion report
- Integration guide
- Example workflows

---

## Conclusion

**Immediate Focus:** Complete Semantic Diff (#889) and Context CLI (#891) this week to reach 42.5% completion.

**Next Milestone:** Complete Canonical Formatter by end of January to reach 50% completion.

**Long-term Goal:** 100% completion by mid-April with comprehensive testing and documentation.

**Success Criteria:**
- ✅ All 40 features implemented
- ✅ 100+ tests passing
- ✅ Complete documentation
- ✅ Production-ready quality
- ✅ LLM-optimized output formats
