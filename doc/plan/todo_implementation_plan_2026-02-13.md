# TODO Implementation Plan - February 2026

**Created:** 2026-02-13
**Status:** Ready for Review
**Total Items:** 530 TODOs/FIXMEs analyzed
**Implementable Now:** 20+ items (2-3 weeks effort)

---

## EXECUTIVE SUMMARY

| Category | Count | % | Status | Action |
|----------|-------|---|--------|--------|
| **Test Assertions (Disabled)** | 468 | 88% | BLOCKED | Wait for compiler phases |
| **Quick Wins** | 20+ | 4% | ✅ READY | Start immediately |
| **Runtime Blocked** | 28 | 5% | BLOCKED | Wait for SFFI/FFI |
| **Obsolete/Review** | 3 | <1% | REVIEW | Minor cleanup |
| **Large Projects** | 2 | <1% | PLANNED | Multi-week efforts |

**Key Finding:** 88% of TODOs are test assertions appropriately disabled pending compiler phase completion. Only 20+ items are immediately actionable as "quick wins".

---

## PHASE 1: QUICK WINS (2-3 weeks) ✅ START HERE

### Week 1: Low-Risk Refactoring (5 days)

#### Day 1-2: bcrypt Module Split
- **File:** `src/std/bcrypt/core.spl`
- **Current:** Monolithic 1000+ lines
- **Split into:**
  - `types.spl` - BcryptHash, Salt types
  - `hash.spl` - Hash generation
  - `verify.spl` - Verification logic
  - `salt.spl` - Salt generation
  - `key_derivation.spl` - Key derivation functions
  - `utilities.spl` - Helper functions
  - `mod.spl` - Public API re-exports
- **Tests:** Verify all existing tests pass
- **Risk:** LOW (pure refactor, no logic changes)

#### Day 3-4: CBOR Module Split
- **File:** `src/std/cbor/core.spl`
- **Apply same pattern as bcrypt**
- **Split into:**
  - `types.spl` - CborValue, CborTag types
  - `encoder.spl` - Encoding logic
  - `decoder.spl` - Decoding logic
  - `utilities.spl` - Helpers
  - `mod.spl` - Public API
- **Tests:** Verify CBOR encode/decode tests
- **Risk:** LOW

#### Day 5: Placeholder Defaults
- **Files:** 6 backend files (interpreter.spl, llvm_backend.spl, etc.)
- **Work:** Replace `nil, # TODO: provide default` with proper defaults
- **Examples:**
  - `default_value: nil # TODO` → `default_value: RuntimeValue.Int(0)`
  - `error_msg: nil # TODO` → `error_msg: "Unknown error"`
- **Count:** ~6-8 instances
- **Risk:** VERY LOW (5-15 minutes each)

### Week 2: Medium-Impact Improvements (5 days)

#### Day 6-7: Backend Type Conversion Helpers
- **File:** `src/compiler/backend/interpreter.spl`
- **Lines:** 785-789
- **TODO:** "Implement full conversion for Array, Dict, etc."
- **Work:**
  ```simple
  match runtime_val:
      RuntimeValue.Array(arr):
          # Convert array elements
      RuntimeValue.Dict(dict):
          # Convert dict entries
      # ... existing cases
  ```
- **Benefit:** Better runtime type debugging
- **Risk:** LOW (additive changes)

#### Day 8-9: Symbol Table Extraction
- **File:** `src/compiler/backend/llvm_backend.spl`
- **TODO:** "Extract symbols from object code"
- **Work:**
  1. Read ELF/MachO/PE object file format
  2. Parse symbol table section
  3. Extract function/variable symbols
  4. Return as `[SymbolInfo]`
- **Use case:** Debugger, profiler, linker support
- **Risk:** MEDIUM (requires binary format knowledge)

#### Day 10: Review & Testing
- Run full test suite
- Verify no regressions
- Document changes

### Week 3: Integration & Polish (5 days)

#### Day 11-12: MCP bugdb Integration
- **File:** `src/app/mcp/bootstrap/main_optimized.spl`
- **TODO:** "Import bugdb handlers when available"
- **Work:**
  1. Import `lib.database.bug` module
  2. Add message handlers: `bug/query`, `bug/add`, `bug/update`
  3. Wire into message routing
  4. Test with MCP client
- **Benefit:** MCP server can query bug database
- **Risk:** MEDIUM-LOW (depends on bugdb API stability)

#### Day 13-14: Async State Machine
- **File:** `src/core/interpreter/eval.spl`
- **TODO:** "Full state machine support requires desugaring"
- **Work:**
  1. Transform `async fn foo() -> T:` into:
     ```simple
     struct FooState:
         stage: i64
         local_vars: ...
         fn poll() -> AsyncResult<T>
     ```
  2. Implement resume logic
  3. Add yield point tracking
- **Benefit:** Proper async/await execution
- **Risk:** MEDIUM-HIGH (complex transformation)

#### Day 15: Final Review
- Documentation updates
- Performance testing
- Commit and report

---

## PHASE 2: BLOCKED ITEMS - TRACK & WAIT (ongoing)

### Item #1: Test Assertions (468 items)
- **Status:** BLOCKED on compiler phases
- **Files:** `test/compiler_core/variance_phase6a.spl` (41), `const_keys_phase8b.spl` (26), etc.
- **Action:** Monitor phase completion
- **When ready:** Uncomment `# TODO: assert` lines, enable tests
- **Effort when ready:** 1-2 days per phase

### Item #2: SFFI Process Timeout (2 items)
- **Files:** `src/app/build/baremetal.spl:307, 315`
- **Status:** BLOCKED on `rt_process_run_timeout` SFFI
- **Action:** Wait for SFFI infrastructure
- **Effort when ready:** 3-5 days

### Item #3: Rust FFI Specs (25 items)
- **File:** `src/app/ffi_gen/specs/im_rs.spl`
- **Status:** C FFI exists; Rust marshalling incomplete
- **Action:** Wait for FFI layer completion
- **Effort when ready:** 2-3 weeks

### Item #4: Runtime Parser Generics
- **Issue:** `<>` syntax fails in interpreter (parse error)
- **Examples:** `GcPtr<T>`, generic libraries
- **Status:** BLOCKED on parser rewrite
- **Action:** Works in compiled mode; document limitation
- **Effort when ready:** 2-4 weeks

### Item #5: Closure Variable Capture
- **Issue:** Can READ outer vars but CANNOT MODIFY
- **Status:** BLOCKED on scope/env rework
- **Action:** Use workarounds (module vars, return values)
- **Effort when ready:** 1-2 weeks

---

## PHASE 3: LARGE PROJECTS (multi-week)

### Project A: Remove `Any` Type (12 weeks)
- **Document:** `doc/todo/remove_any_type.md`
- **Scope:** 85 files using `Any` type
- **Sub-phases:**
  1. Concurrency Runtime FFI (4 weeks)
  2. Compiler Type System (6 weeks)
  3. Test Files (1 week)
  4. Type Alias Removal (1 week)
- **Benefits:** Type safety, performance, maintainability
- **Risk:** HIGH (breaking changes, 85 files affected)
- **Owner:** TBD
- **Start:** Q2 2026 (after Phase 1 complete)

### Project B: Next Session Priorities
- **Document:** `doc/TODO_NEXT_SESSION.md` (Feb 3, 2026 - OUTDATED)
- **Status:** Review and update based on current state
- **Key items:**
  - Module system enhancement (may be resolved)
  - Circular dependency fix (verify status)
  - Test suite verification
- **Action:** Create updated priorities document

---

## PHASE 4: CLEANUP (1 day)

### Obsolete TODOs Review
- **File:** `src/app/build/bootstrap_simple.spl`
- **TODO:** "Implement full 3-stage bootstrap"
- **Action:** Review if still needed; remove if obsolete
- **Effort:** 1 day (decision + cleanup)

---

## IMPLEMENTATION ORDER

### Recommended Sequence

**This Week (Feb 13-17):**
1. ✅ bcrypt module split (Day 1-2)
2. ✅ CBOR module split (Day 3-4)
3. ✅ Placeholder defaults (Day 5)

**Next Week (Feb 18-22):**
4. ✅ Backend type conversion (Day 6-7)
5. ✅ Symbol table extraction (Day 8-9)
6. ✅ Review & testing (Day 10)

**Week 3 (Feb 25-Mar 1):**
7. ✅ MCP bugdb integration (Day 11-12)
8. ✅ Async state machine (Day 13-14)
9. ✅ Final review (Day 15)

**Ongoing:**
- Monitor compiler phase completion
- Track SFFI infrastructure work
- Update blocked items when ready

---

## SUCCESS METRICS

### Phase 1 Complete When:
- [ ] bcrypt module: 7 files, all tests passing
- [ ] CBOR module: 5 files, all tests passing
- [ ] Placeholder defaults: 6-8 instances fixed
- [ ] Backend conversions: Array/Dict cases added
- [ ] Symbol extraction: Basic ELF support working
- [ ] MCP bugdb: Query/add/update handlers functional
- [ ] Async state machine: Basic async/await works
- [ ] Full test suite: 604/604 passing (no regressions)

### Phase 2 Monitoring:
- [ ] Compiler phases: Track completion percentage
- [ ] SFFI: rt_process_run_timeout added
- [ ] FFI: Rust marshalling layer complete
- [ ] Parser: Generic support in runtime parser
- [ ] Closures: Variable capture fixed

### Phase 3 Planning:
- [ ] "Remove Any" project: Owner assigned, start date set
- [ ] Next session priorities: Updated document created

---

## RISK ASSESSMENT

| Item | Risk | Mitigation |
|------|------|------------|
| bcrypt/CBOR split | LOW | Pure refactor, no logic changes, comprehensive tests |
| Placeholder defaults | VERY LOW | Trivial changes, localized impact |
| Backend conversions | LOW | Additive changes, optional functionality |
| Symbol extraction | MEDIUM | Requires binary format knowledge, use existing libraries |
| MCP integration | MEDIUM-LOW | Depends on bugdb API, test thoroughly |
| Async state machine | MEDIUM-HIGH | Complex transformation, start with simple cases |
| Test regressions | LOW | Full test suite run after each change |

---

## DEPENDENCIES

### Internal Dependencies
- **None for Phase 1** - All quick wins are independent
- Phase 2 depends on infrastructure work (SFFI, FFI, parser)
- Phase 3 depends on Phase 1 completion

### External Dependencies
- Runtime team: SFFI/FFI infrastructure
- Compiler team: Phase completion (variance, const eval, etc.)
- Parser team: Generic syntax support

---

## RESOURCES NEEDED

### Development Time
- Phase 1: 15 days (3 weeks)
- Phase 2: Ongoing monitoring (1-2 hours/week)
- Phase 3: 12 weeks (for "Remove Any" project)

### Testing
- Full test suite runs: ~5-10 minutes each
- Integration testing: ~30 minutes per major change
- Performance benchmarks: ~15 minutes

### Documentation
- Update MEMORY.md: Track completed items
- Update TODO.md: Run `bin/simple todo-scan` after each phase
- Create completion report: Document changes and metrics

---

## COMPLETION REPORT TEMPLATE

When Phase 1 is complete, create `doc/report/todo_phase1_complete_2026-02-XX.md` with:

```markdown
# TODO Phase 1 Implementation Complete

## Summary
- Duration: XX days (Feb 13 - Feb XX, 2026)
- Items completed: 20+
- Files changed: ~XX
- Lines added/modified: ~XXX
- Test suite: 604/604 passing (no regressions)

## Changes
1. bcrypt module: Split into 7 files
2. CBOR module: Split into 5 files
3. Placeholder defaults: 8 instances fixed
4. Backend conversions: Array/Dict support added
5. Symbol extraction: Basic ELF support
6. MCP bugdb: 3 handlers added
7. Async state machine: Basic support

## Metrics
- TODO count: 530 → 510 (20 resolved)
- Code organization: +12 new modules
- Test coverage: Maintained at 100% (604/604)
- Performance: No regressions (<1% variance)

## Next Steps
- Begin Phase 2 monitoring
- Plan Phase 3 projects
- Update MEMORY.md
```

---

## QUESTIONS FOR USER

Before starting implementation:

1. **Priority confirmation:** Start with bcrypt/CBOR split (Week 1)?
2. **Async state machine:** Include in Phase 1 or defer to Phase 2?
3. **Symbol extraction:** Use external ELF library or implement from scratch?
4. **MCP integration:** Required now or can wait?
5. **Test regression tolerance:** 0 failures or allow minor issues?

---

## CONCLUSION

This plan provides a clear, actionable roadmap for implementing 20+ TODO items over 3 weeks. The work is low-risk, provides immediate value, and sets the foundation for larger projects. All items are independent and can be implemented in parallel if multiple developers are available.

**Recommended Action:** Review and approve Phase 1 plan, then start with Week 1 (bcrypt/CBOR split + placeholder defaults).

---

**Document Owner:** Claude Code
**Reviewers:** User
**Approval:** Pending
**Start Date:** TBD (After approval)
