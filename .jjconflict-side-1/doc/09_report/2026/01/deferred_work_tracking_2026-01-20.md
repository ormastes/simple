# Deferred Work Tracking - Rust to Simple Migrations

**Date:** 2026-01-20
**Status:** ACTIVE TRACKING
**Purpose:** Track deferred work, blockers, and future migration candidates

---

## Quick Reference

| Category | Count | Priority | Status |
|----------|-------|----------|--------|
| **FFI Implementations** | 3 functions | P2 | Ready to implement |
| **Test Coverage** | 3 files | P1 | Can do now |
| **Language Features** | 6 proposals | P0-P2 | Compiler team |
| **Blocked Migrations** | ~15 files | P3 | Wait for fixes |
| **Ready Migrations** | ~8 files | P1 | Can do now |

---

## Section 1: FFI Implementations (Deferred - P2)

### Why Deferred
These require runtime changes and are not critical for standalone testing.

### 1.1 arg_parsing.spl FFI Functions

**File:** `src/runtime/src/value/compiler_control.rs` (create new)

**Functions needed:**
```rust
// Enable/disable macro expansion tracing
pub fn rt_set_macro_trace(enabled: bool) {
    // TODO: Set global flag for macro tracing
}

// Enable/disable debug mode
pub fn rt_set_debug_mode(enabled: bool) {
    // TODO: Set global debug flag
}
```

**Current behavior:**
```simple
# Stubs in arg_parsing.spl
fn apply():
    if macro_trace:
        print "[arg_parsing] macro_trace enabled (FFI stub)"
    if debug_mode:
        print "[arg_parsing] debug_mode enabled (FFI stub)"
```

**Implementation checklist:**
- [ ] Create `src/runtime/src/value/compiler_control.rs`
- [ ] Implement `rt_set_macro_trace(bool)`
- [ ] Implement `rt_set_debug_mode(bool)`
- [ ] Add FFI bindings in Simple runtime
- [ ] Update `arg_parsing.spl` to call real FFI
- [ ] Test with actual compiler behavior

**Priority:** P2 (not needed for testing, only for production use)

---

### 1.2 sandbox.spl FFI Functions

**File:** `src/runtime/src/value/sandbox.rs` (may already exist)

**Function needed:**
```rust
pub fn rt_apply_sandbox(config: &SandboxConfig) -> Result<(), String> {
    // Apply CPU time limit
    if let Some(secs) = config.time_limit_secs {
        // Set rlimit RLIMIT_CPU
    }
    
    // Apply memory limit
    if let Some(bytes) = config.memory_limit_bytes {
        // Set rlimit RLIMIT_AS
    }
    
    // Apply file descriptor limit
    if let Some(fds) = config.fd_limit {
        // Set rlimit RLIMIT_NOFILE
    }
    
    // Apply network restrictions
    if config.no_network {
        // Use seccomp or similar
    }
    
    Ok(())
}
```

**Current behavior:**
```simple
# Stub in sandbox.spl
fn apply_sandbox(config: SandboxConfig) -> Result<(), text>:
    print "[sandbox] Would apply sandbox config (FFI stub)"
    Ok(())
```

**Implementation checklist:**
- [ ] Check if `src/runtime/src/value/sandbox.rs` exists
- [ ] Implement resource limit setting (rlimit)
- [ ] Implement network restrictions (seccomp/landlock)
- [ ] Implement file path restrictions
- [ ] Add FFI bindings in Simple runtime
- [ ] Update `sandbox.spl` to call real FFI
- [ ] Test with actual sandboxed processes

**Priority:** P2 (testing works without this, production needs it)

**Security note:** This is critical for production sandbox security!

---

### 1.3 FFI Implementation Guidelines

**General approach:**
1. Create Rust function in appropriate runtime module
2. Add `#[no_mangle]` and `extern "C"` for FFI
3. Register in Simple runtime's FFI table
4. Update Simple code to call FFI instead of stub
5. Test with integration tests

**Example pattern:**
```rust
// In runtime
#[no_mangle]
pub extern "C" fn rt_set_macro_trace(enabled: bool) {
    unsafe {
        MACRO_TRACE_ENABLED = enabled;
    }
}
```

```simple
// In Simple (updated)
fn apply():
    if macro_trace:
        ffi_call("rt_set_macro_trace", [true])
```

---

## Section 2: Test Coverage (Deferred - P1)

### Why Deferred
Basic tests exist, but comprehensive coverage was blocked by:
- Match expressions in test contexts (syntax issues)
- Import system not fully working for tests
- Time constraints

### 2.1 arg_parsing_spec.spl - ADEQUATE

**Current:** 84 lines, 12+ test cases
**Coverage:** ~80% of functionality

**Missing tests:**
- Edge cases for filter_internal_flags (empty lists, all flags)
- Error handling for parse_lang_flag
- Integration with actual command parsing

**Priority:** P2 (current coverage is good enough)

---

### 2.2 sandbox_spec.spl - MINIMAL ⚠️

**Current:** 6 lines, 1 basic sanity check
**Coverage:** ~5% of functionality

**Missing tests:**
- [ ] parse_memory_size with all suffixes (K, M, G)
- [ ] parse_memory_size error cases
- [ ] parse_sandbox_config with all flag combinations
- [ ] SandboxConfig builder method chaining
- [ ] Network allowlist/blocklist parsing
- [ ] Path list parsing (comma-separated)

**Implementation plan:**
```simple
describe "parse_memory_size comprehensive":
    describe "parses all suffixes":
        it "1024 bytes": expect parse_memory_size("1024").unwrap() == 1024
        it "512K": expect parse_memory_size("512K").unwrap() == 524288
        it "256M": expect parse_memory_size("256M").unwrap() == 268435456
        it "2G": expect parse_memory_size("2G").unwrap() == 2147483648
    
    describe "handles errors":
        it "rejects invalid": expect parse_memory_size("invalid").is_err()
        it "rejects empty": expect parse_memory_size("").is_err()
```

**Blocker:** Match expressions in test context don't work well
**Workaround:** Use helper functions or simpler assertions

**Priority:** P1 (should be done before production use)

---

### 2.3 test_args_spec.spl - MINIMAL ⚠️

**Current:** 5 lines, 1 basic sanity check
**Coverage:** ~2% of functionality

**Missing tests:**
- [ ] All 30+ CLI flags
- [ ] Flag combinations
- [ ] Value flag parsing (--tag, --seed, --format)
- [ ] Path argument handling
- [ ] Default values verification
- [ ] Enum comparisons (TestLevel, OutputFormat)

**Implementation plan:**
```simple
describe "parse_test_args comprehensive":
    describe "test level flags":
        it "parses --unit": 
            val opts = parse_test_args(["--unit"])
            expect opts.level == TestLevel::Unit
        
        it "parses --integration":
            val opts = parse_test_args(["--integration"])
            expect opts.level == TestLevel::Integration
    
    describe "boolean flags":
        it "parses --fail-fast":
            val opts = parse_test_args(["--fail-fast"])
            expect opts.fail_fast == true
        
        it "parses --watch":
            val opts = parse_test_args(["--watch"])
            expect opts.watch == true
    
    describe "format flags":
        it "parses --json":
            val opts = parse_test_args(["--json"])
            expect opts.format == OutputFormat::Json
```

**Priority:** P1 (important for CLI reliability)

---

### 2.4 Test Coverage Checklist

**For each migrated file:**
- [ ] Unit tests for all public functions
- [ ] Edge case tests (empty input, invalid input, boundary conditions)
- [ ] Integration tests (if applicable)
- [ ] Property-based tests (if using property testing framework)

**Test quality standards:**
- Coverage: >80% for production code
- Edge cases: All error paths tested
- Documentation: Each test describes what it validates

---

## Section 3: Language Features (Deferred - Compiler Team)

### 3.1 Priority 0 - CRITICAL BLOCKERS

#### P0.1: Struct Update Syntax 🔥🔥🔥

**Impact:** Blocks ~30% of Rust patterns
**Evidence:** sandbox.rs expanded 171% due to lack of this

**Current problem:**
```simple
# Must copy ALL fields when changing ONE
fn with_memory(bytes: u64) -> SandboxConfig:
    SandboxConfig(
        time_limit_secs: time_limit_secs,     # Copy
        memory_limit_bytes: Some(bytes),      # Change
        fd_limit: fd_limit,                   # Copy
        thread_limit: thread_limit,           # Copy
        no_network: no_network,               # Copy
        network_allowlist: network_allowlist, # Copy
        network_blocklist: network_blocklist, # Copy
        read_paths: read_paths,               # Copy
        write_paths: write_paths              # Copy
    )
```

**Proposed solutions:**

**Option A - Rust style:**
```simple
fn with_memory(bytes: u64) -> SandboxConfig:
    SandboxConfig {
        memory_limit_bytes: Some(bytes),
        ..self  # Copy remaining fields
    }
```

**Option B - Shorter:**
```simple
fn with_memory(bytes: u64) -> SandboxConfig:
    SandboxConfig(..self, memory_limit_bytes: Some(bytes))
```

**Option C - Explicit:**
```simple
fn with_memory(bytes: u64) -> SandboxConfig:
    self.copy(memory_limit_bytes: Some(bytes))
```

**Estimated impact:**
- sandbox.spl: 255 → 120 lines (53% reduction)
- Any builder pattern: 15x → 1.5x code ratio

**Recommendation:** Option B (shortest, clearest intent)

**Implementation complexity:** Medium
- Parser changes needed
- Type checker needs to verify field names
- Codegen needs to copy struct and update fields

**Status:** Proposal ready, needs compiler team decision

---

### 3.2 Priority 1 - IMPORTANT QOL

#### P1.1: Multi-line Boolean Expressions

**Impact:** Readability for complex conditions

**Current limitation:**
```simple
# Must be single line (ugly!)
val is_flag = arg.starts_with("--gc") or arg == "--notui" or arg == "--startup-metrics" or arg == "--macro-trace"
```

**Proposed:**
```simple
val is_flag = (
    arg.starts_with("--gc") or
    arg == "--notui" or
    arg == "--startup-metrics" or
    arg == "--macro-trace"
)
```

**Implementation:** Parser needs to allow newlines in expressions within parens

---

#### P1.2: Derived Default Trait

**Impact:** Reduces boilerplate for default constructors

**Current:**
```simple
# Must write manually (28 lines for TestOptions)
static fn default() -> TestOptions:
    TestOptions(
        path: None,
        level: TestLevel::All,
        tag: None,
        fail_fast: false,
        # ... 20 more fields
    )
```

**Proposed:**
```simple
#[derive(Default)]
struct TestOptions:
    path: Option<text> = None
    level: TestLevel = TestLevel::All
    tag: Option<text> = None
    fail_fast: bool = false
    # ... default values inline
```

---

#### P1.3: Field Name Shortcuts

**Impact:** Reduces repetition in constructors

**Current:**
```simple
fn new(x: i32, y: i32) -> Point:
    Point(x: x, y: y)  # Repetitive
```

**Proposed:**
```simple
fn new(x: i32, y: i32) -> Point:
    Point(x, y)  # Infer field names from variables
```

---

### 3.3 Priority 2 - NICE TO HAVE

#### P2.1: Match in Assignment Context

**Problem:** Can't assign in match arms
**Workaround:** Use if/unwrap

**Current:**
```simple
val maybe_seed = args[i].parse_u64()
if maybe_seed.is_ok():
    options.seed = Some(maybe_seed.unwrap())
```

**Desired:**
```simple
match args[i].parse_u64():
    Ok(seed) => options.seed = Some(seed)
    Err(_) => ()
```

---

#### P2.2: Result.ok() Method

**Problem:** No ergonomic Result → Option conversion

**Current:** Multiple lines
**Proposed:** `options.seed = args[i].parse_u64().ok()`

---

#### P2.3: String Literal Improvements

**Minor issues:**
- Raw strings (`r"..."`) support
- Multi-line strings
- String interpolation edge cases

---

## Section 4: Blocked Migrations (Deferred - P3)

### Why Blocked
These patterns require language features (mainly struct update syntax) that don't exist yet.

### 4.1 Builder Pattern Files (BLOCKED - Need P0.1)

**Files identified:**

1. **Configuration builders** (~5-8 files estimated)
   - Any file with builder pattern
   - Immutable data structures
   - Fluent APIs

2. **Type builders** (compiler internal types)
   - HIR/MIR builders
   - Type construction helpers
   - AST builders

**Estimated impact without struct update syntax:**
- Each file: +100-200% code expansion
- Not practical to migrate

**Status:** WAIT for P0.1 feature

---

### 4.2 HashMap-Heavy Code (BLOCKED - Need investigation)

**Files identified:**

1. **lint/config.rs** (auto-created, 255 lines)
   - Uses HashMap<LintName, LintLevel>
   - Unclear if Simple's Map API is verbose

2. **Symbol tables / scopes**
   - HashMap<String, Symbol>
   - May have similar issues

**Status:** INVESTIGATE Simple's HashMap/Map API first

**Action items:**
- [ ] Read Simple Map API documentation
- [ ] Create proof-of-concept Map usage
- [ ] Determine if Map is practical for these patterns

---

### 4.3 Complex Type Dependencies (BLOCKED - Need stubs)

**Files identified:**

1. **Type system utilities**
   - Files depending on complex compiler types
   - Files using AST/HIR/MIR types

2. **Parser utilities**
   - Files depending on parsing infrastructure
   - Token manipulation utilities

**Status:** Need to create type stubs or mock objects

**Workaround:** Create minimal type stubs in Simple for testing

---

## Section 5: Ready Migrations (Ready Now - P1)

### Why Ready
These follow successful patterns (boolean flags, string processing, mutable structs).

### 5.1 CLI Utilities (READY - Pattern: test_args)

**Files ready for migration:**

1. **build_args.rs** (~100 lines estimated)
   - CLI argument parsing for build command
   - Pattern: Mutable struct like test_args
   - Expected: +10-20% expansion

2. **run_args.rs** (~80 lines estimated)
   - CLI argument parsing for run command
   - Pattern: Boolean flags like arg_parsing
   - Expected: -20-30% reduction

3. **format_args.rs** (~60 lines estimated)
   - CLI argument parsing for format command
   - Pattern: Simple flag parsing
   - Expected: -25-35% reduction

**Total estimated:** ~240 Rust lines → ~230 Simple lines

---

### 5.2 String Utilities (READY - Pattern: arg_parsing)

**Files ready for migration:**

1. **path_utils.rs** (~120 lines)
   - Path manipulation utilities
   - String processing heavy
   - Expected: -15-25% reduction

2. **string_helpers.rs** (~90 lines)
   - String transformation utilities
   - Simple's string API excels here
   - Expected: -20-30% reduction

3. **escape_utils.rs** (~70 lines)
   - HTML/JSON escaping
   - String processing
   - Expected: -10-20% reduction

**Total estimated:** ~280 Rust lines → ~230 Simple lines

---

### 5.3 Simple Data Transformers (READY - Pattern: mixed)

**Files ready for migration:**

1. **file_discovery.rs** (~150 lines)
   - Find files by pattern
   - List operations + string matching
   - Expected: -5-15% reduction

2. **version_parser.rs** (~80 lines)
   - Parse semantic versions
   - String parsing + validation
   - Expected: 0-10% reduction

**Total estimated:** ~230 Rust lines → ~220 Simple lines

---

### 5.4 Migration Priority Order

**Recommend this order:**

1. **format_args.rs** (easiest, high confidence)
2. **run_args.rs** (similar to arg_parsing)
3. **escape_utils.rs** (good for string API showcase)
4. **path_utils.rs** (useful utility)
5. **build_args.rs** (after testing mutable pattern)

**Estimated time:** 3-4 hours for all 5 files

---

## Section 6: Implementation Roadmap

### Phase 1: Test Coverage (1-2 hours)

**Goal:** Bring existing migrations to 80%+ test coverage

**Tasks:**
1. Expand sandbox_spec.spl
   - Add parse_memory_size tests (all cases)
   - Add parse_sandbox_config tests (flag combinations)
   - Add builder tests

2. Expand test_args_spec.spl
   - Add tests for all 30+ flags
   - Add combination tests
   - Add default value tests

3. Keep arg_parsing_spec.spl as-is (already good)

**Deliverable:** 3 comprehensive test files

---

### Phase 2: Easy Wins (2-3 hours)

**Goal:** Migrate 5 more files using proven patterns

**Tasks:**
1. Migrate format_args.rs
2. Migrate run_args.rs  
3. Migrate escape_utils.rs
4. Migrate path_utils.rs
5. Migrate build_args.rs

**Deliverable:** 5 new Simple files + tests + reports

---

### Phase 3: FFI Implementation (4-6 hours)

**Goal:** Connect Simple code to runtime

**Tasks:**
1. Implement compiler_control.rs
   - rt_set_macro_trace()
   - rt_set_debug_mode()

2. Implement/verify sandbox.rs
   - rt_apply_sandbox()
   - Resource limits (rlimit)
   - Network restrictions (seccomp)

3. Update Simple files to use real FFI

4. Integration tests

**Deliverable:** Working FFI, production-ready sandbox

---

### Phase 4: Language Features (Compiler team - TBD)

**Goal:** Unblock builder pattern migrations

**Tasks:**
1. Design struct update syntax (Option B recommended)
2. Implement parser changes
3. Implement type checker support
4. Implement codegen
5. Add tests
6. Update documentation

**Deliverable:** Struct update syntax feature

---

### Phase 5: Blocked Migrations (After Phase 4)

**Goal:** Migrate builder pattern files

**Tasks:**
1. Re-attempt sandbox.rs with new syntax
2. Migrate configuration builders
3. Migrate type builders
4. Update migration report with new metrics

**Deliverable:** 15+ additional migrated files

---

## Section 7: Tracking & Metrics

### Migration Progress Tracker

| File | LOC | Pattern | Status | Blocker | Priority |
|------|-----|---------|--------|---------|----------|
| arg_parsing.rs | 126 | Boolean flags | ✅ Done | - | - |
| sandbox.rs | 94 | Builder | ✅ Done¹ | P0.1 | - |
| test_args.rs | 169 | Mutable struct | ✅ Done | - | - |
| lint_config.rs | 124 | HashMap | ✅ Auto² | Need review | P2 |
| format_args.rs | ~60 | Flags | 📋 Ready | - | P1 |
| run_args.rs | ~80 | Flags | 📋 Ready | - | P1 |
| escape_utils.rs | ~70 | Strings | 📋 Ready | - | P1 |
| path_utils.rs | ~120 | Strings | 📋 Ready | - | P1 |
| build_args.rs | ~100 | Mutable | 📋 Ready | - | P1 |

¹ Works but verbose; will redo after P0.1
² Auto-created by linter; needs verification

**Legend:**
- ✅ Done: Migrated and tested
- 📋 Ready: Can migrate now
- ⏸️ Deferred: Waiting for features
- ❌ Blocked: Cannot migrate yet

---

### Test Coverage Tracker

| File | Current | Target | Missing | Priority |
|------|---------|--------|---------|----------|
| arg_parsing_spec | 80% | 80% | ✅ Good | P2 |
| sandbox_spec | 5% | 80% | 75% | P1 |
| test_args_spec | 2% | 80% | 78% | P1 |

---

### FFI Implementation Tracker

| Function | File | Status | Priority | Estimate |
|----------|------|--------|----------|----------|
| rt_set_macro_trace | compiler_control.rs | 📋 Todo | P2 | 30min |
| rt_set_debug_mode | compiler_control.rs | 📋 Todo | P2 | 30min |
| rt_apply_sandbox | sandbox.rs | 📋 Todo | P2 | 3-4h |

---

## Section 8: Decision Log

### Decision 1: Mutable Struct > Builder Pattern
**Date:** 2026-01-20
**Decision:** Use `var struct` + field mutation instead of builder pattern
**Rationale:** test_args proved this is more concise (-4% vs Rust)
**Impact:** Makes Simple more ergonomic for this common pattern

### Decision 2: Inline Type Definitions
**Date:** 2026-01-20
**Decision:** Define enums/structs inline in same file (for now)
**Rationale:** Simpler, no module complexity, good for prototyping
**Future:** May extract to separate modules later

### Decision 3: Defer Comprehensive Tests
**Date:** 2026-01-20
**Decision:** Ship with basic tests, expand later
**Rationale:** Match expression syntax issues, time constraints
**Mitigation:** Track in this document, prioritize P1

### Decision 4: FFI Stubs Acceptable
**Date:** 2026-01-20
**Decision:** Ship with print stubs, implement FFI later
**Rationale:** Testing doesn't need FFI, production does
**Timeline:** Implement in Phase 3

---

## Section 9: Next Actions

### Immediate (Next session)

1. **Expand test coverage** (1-2 hours)
   - sandbox_spec.spl: Add comprehensive tests
   - test_args_spec.spl: Add comprehensive tests

2. **Migrate easy wins** (2-3 hours)
   - format_args.rs → format_args.spl
   - run_args.rs → run_args.spl

### Short-term (This week)

3. **Complete easy migrations** (2-3 hours)
   - escape_utils.rs, path_utils.rs, build_args.rs

4. **Document patterns** (1 hour)
   - Create migration pattern cookbook
   - Update guidelines with test examples

### Medium-term (This month)

5. **FFI implementation** (4-6 hours)
   - Implement compiler_control.rs
   - Implement/verify sandbox.rs
   - Integration tests

6. **Investigate HashMap** (1-2 hours)
   - Test Simple's Map API
   - Determine if lint_config needs rework

### Long-term (Waiting on compiler team)

7. **Language features**
   - P0.1: Struct update syntax
   - P1.1-P1.3: QOL improvements
   - P2.1-P2.3: Nice-to-haves

8. **Blocked migrations**
   - Retry sandbox with new syntax
   - Migrate builder pattern files

---

## Section 10: Contact & Communication

### For questions about:

**Migration strategy:** See this document
**Test patterns:** See test_args migration report
**Language features:** File GitHub issue with P0/P1/P2 label
**FFI implementation:** Check runtime documentation

### Reporting issues:

**Migration bugs:** File with `migration` label
**Language gaps:** File with `language-feature` label
**Documentation:** File with `docs` label

---

**Document Status:** ACTIVE TRACKING
**Last Updated:** 2026-01-20
**Next Review:** After Phase 1 completion

---

**Summary:** 
- ✅ 4 files migrated
- 📋 5 files ready for migration
- ⏸️ 2 items deferred (tests, FFI)
- ❌ ~15 files blocked (waiting for P0.1)
- 🔥 1 critical blocker (struct update syntax)
