# TODO Implementation Plan - REVISED after Reality Check

**Date:** 2026-02-09
**Status:** Phase 1 Investigation Required
**Previous Plan:** `TODO_IMPLEMENTATION_PLAN.md` (outdated)

## 🚨 Critical Discovery

**The planned FFI functions DO NOT EXIST in the runtime.**

Original plan assumed we could add:
- `rt_string_from_ptr_len(ptr, len) -> text`
- `rt_string_to_ptr(s) -> i64`
- etc.

**Reality:** These are not in `bin/bootstrap/simple` runtime. Can't add without recompiling Rust.

## Current Status

### ✅ Completed (3 TODOs)

**Pure Simple string helpers** in `src/app/io/mod.spl`:
- `hex_to_char(code: i64) -> text` - Converts hex to character
- `byte_to_char(byte: i64) -> text` - Converts byte to character
- `char_code(c: text) -> i64` - Gets character code

TODOs addressed: #95 (lexer), #106 (smf_reader)

### ❌ Blocked (9 TODOs)

**Interpreter string FFI** (#41-48, #50):
- Require extracting ptr+len from Simple strings
- No runtime builtin exists for this
- Current code uses placeholder `0` for pointers (broken?)

**Options:**
1. **Investigate first** - Maybe auto-conversion exists?
2. **Use high-level API** - Don't use low-level ptr+len FFI
3. **Document limitation** - Mark as "requires runtime enhancement"
4. **Skip for now** - Focus on TODOs we CAN fix

## Revised Phase 1: Reality-Based Approach

### Phase 1A: Investigation (1-2 days) 🔍

**Goal:** Understand how string FFI actually works

**Tasks:**
1. Test current FFI behavior
2. Find working examples in codebase
3. Check if Simple auto-converts strings to ptr+len
4. Document findings

**Deliverables:**
- `doc/report/string_ffi_investigation_2026-02-09.md`
- Updated MEMORY.md with FFI limitations
- Decision on interpreter TODOs

### Phase 1B: Implementable TODOs (3-5 days) ⚪

**Skip problematic FFI**, focus on Pure Simple implementations:

**Memory helpers** (if possible without FFI):
- Hex/byte conversions ✅ DONE
- String formatting helpers
- Array/collection utilities

**Parser helpers:**
- SDN parsing (use existing stdlib)
- JSON parsing (use existing stdlib)
- CSV/TOML basic implementations

**Est. TODOs:** ~20-30 (avoid FFI-dependent ones)

### Phase 1C: Document Limitations (1 day) 📝

**Goal:** Clear documentation of what's blocked

**Create:**
- List of TODOs requiring runtime changes
- Workarounds where possible
- Feature requests for future runtime

## New TODO Categorization

### Category A: Pure Simple (No FFI) - ~150 TODOs
Can implement immediately:
- Parser improvements
- Type checking enhancements
- Code generation (where not FFI-dependent)
- Stdlib Pure Simple code

### Category B: Existing FFI (Use what exists) - ~100 TODOs
Use current runtime builtins:
- File I/O (high-level API)
- Process operations
- Environment variables
- Time/date functions

### Category C: Missing FFI (Blocked) - ~80 TODOs
Require runtime enhancements:
- String ptr+len extraction
- Memory operations (mmap, etc.)
- Advanced syscalls
- JIT memory management

### Category D: Stub/Future (Low priority) - ~53 TODOs
Nice-to-have features:
- Advanced backends
- Optimization passes
- Tool integrations

## Immediate Next Steps

1. **Today:**
   - ✅ Add Pure Simple helpers (DONE)
   - 🔍 Run string FFI investigation
   - 📝 Write investigation report

2. **Tomorrow:**
   - Based on investigation, decide on interpreter TODOs
   - Start Phase 1B (implementable TODOs)
   - Update main plan

3. **This Week:**
   - Complete Phase 1B (Pure Simple implementations)
   - Document all limitations
   - Prepare Phase 2 (Parser improvements - mostly Pure Simple)

## Revised Timeline

**Phase 1 (Current):** 1 week
- Investigation: 1-2 days
- Pure Simple helpers: 3-4 days
- Documentation: 1 day

**Phase 2 (Parser):** 2 weeks
- Pure Simple implementations
- No FFI dependencies
- ~40-50 TODOs achievable

**Phase 3 (Codegen):** 2-3 weeks
- Mix of Pure Simple and existing FFI
- ~30-40 TODOs achievable

**Blocked Items:** ~80 TODOs
- Requires runtime recompilation
- Out of scope for current session
- Document for future work

## Success Metrics (Revised)

- [x] 3 TODOs complete (Pure Simple helpers)
- [ ] String FFI investigation complete
- [ ] 20-30 more TODOs (Pure Simple only)
- [ ] All limitations documented
- [ ] Test suite still 330/330 passing
- [ ] Clear path forward for Category A/B TODOs

## Files Modified

### Completed
- `src/app/io/mod.spl` - Added hex_to_char, byte_to_char, char_code

### Investigation Needed
- `src/compiler/backend/interpreter.spl` - String FFI TODOs
- `src/compiler/ffi_minimal.spl` - Check wrapper patterns
- Runtime (if accessible) - Check string implementation

### Next to Modify (Phase 1B)
- Parser helpers (Pure Simple)
- SDN/JSON integration (use existing stdlib)
- Type system improvements (Pure Simple)
