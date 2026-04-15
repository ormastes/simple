# TODO Implementation Plan - 383 TODOs in 7 Phases

**Created:** 2026-02-09
**Status:** In Progress - Phase 1
**Total TODOs:** 383
**Agent ID:** ad4028d (for resuming planning work)

## Quick Status

| Phase | TODOs | Status | Duration | Priority |
|-------|-------|--------|----------|----------|
| **Phase 1: FFI & String Infrastructure** | 48 | 🟢 **IN PROGRESS** | 2-3 weeks | CRITICAL |
| Phase 2: Parser & Lexer Enhancements | 52 | ⚪ Pending | 2-3 weeks | HIGH |
| Phase 3: MIR Optimization & Codegen | 45 | ⚪ Pending | 3-4 weeks | HIGH |
| Phase 4: Monomorphization & Generics | 38 | ⚪ Pending | 3-4 weeks | MEDIUM |
| Phase 5: Module System & Linking | 42 | ⚪ Pending | 2-3 weeks | MEDIUM |
| Phase 6: Runtime & Backend Infrastructure | 68 | ⚪ Pending | 4-5 weeks | LOW-MEDIUM |
| Phase 7: Advanced Features & Polish | 90 | ⚪ Pending | 5-6 weeks | LOW |

## Phase 1: Foundation - FFI & String Infrastructure (48 TODOs)

**Goal:** Implement core FFI layer and string/memory operations that unlock ~150 downstream TODOs.

### 1.1 String Conversion FFI (12 TODOs) ✅ PRIORITY 1

**Why first:** Blocks parser improvements, SMF reader, interpreter FFI calls

**Files to modify:**
- `src/app/io/mod.spl` - Add FFI function declarations
- `src/compiler/backend/interpreter.spl` - Use new FFI functions (TODOs #41-48)
- `src/compiler/lexer.spl:514` - Hex to char conversion (TODO #95)
- `src/compiler/linker/smf_reader.spl:345` - Byte to char conversion (TODO #106)

**Implementation:**
```simple
# In src/app/io/mod.spl - add these FFI functions
extern fn rt_string_from_ptr_len(ptr: i64, len: i64) -> text
extern fn rt_string_to_ptr_len(s: text) -> (i64, i64)
extern fn rt_hex_to_char(hex: text) -> text
extern fn rt_byte_to_char(byte: i64) -> text

# Create wrapper functions
fn string_from_ptr(ptr: i64, len: i64) -> text:
    rt_string_from_ptr_len(ptr, len)

fn string_to_ptr(s: text) -> (i64, i64):
    rt_string_to_ptr_len(s)

fn hex_to_char(hex: text) -> text:
    rt_hex_to_char(hex)

fn byte_to_char(byte: i64) -> text:
    rt_byte_to_char(byte)
```

**TODOs addressed:**
- #41-48: Proper string ptr+len conversion in `interpreter.spl`
- #95: Hex to char conversion in `lexer.spl`
- #106: Byte-to-char conversion in `smf_reader.spl`

### 1.2 Memory Operations FFI (8 TODOs) ⚪ PRIORITY 2

**Why second:** Unblocks GC implementation, JIT compilation, SMF hot reload

**Files to modify:**
- `src/app/io/mod.spl` - Add memory FFI functions
- `src/app/gc/core.spl` - Use memory operations (TODOs #5-8)
- `src/compiler/loader/jit_instantiator.spl` - Enable mmap functions (TODOs #113-114)
- `src/compiler/loader/smf_cache.spl` - Add mmap support (TODO #118)

**Implementation:**
```simple
# Memory operations
extern fn rt_mem_read(addr: i64, size: i64) -> [i64]
extern fn rt_mem_write(addr: i64, data: [i64])
extern fn rt_mmap(path: text, size: i64) -> i64
extern fn rt_munmap(addr: i64, size: i64) -> bool
extern fn rt_mprotect_exec(addr: i64, size: i64) -> bool

# Wrappers
fn mem_read(addr: i64, size: i64) -> [i64]:
    rt_mem_read(addr, size)

fn mem_write(addr: i64, data: [i64]):
    rt_mem_write(addr, data)
```

**TODOs addressed:**
- #5-8: Memory read/write in `gc/core.spl`
- #113-114: Enable jit_instantiator functions
- #118: Enable smf_cache functions

### 1.3 File I/O Extensions (10 TODOs) ⚪ PRIORITY 3

**Why third:** Enables package verification, hot reload, module resolution

**Files to modify:**
- `src/app/io/mod.spl` - Add file I/O FFI
- `src/compiler/monomorphize/hot_reload.spl` - Offset file ops (TODOs #162-163)
- `src/compiler/module_resolver/` - Dir scanning (TODOs #102, #377)

**Implementation:**
```simple
extern fn rt_process_run_timeout(cmd: text, args: [text], timeout_ms: i64) -> (text, text, i64)
extern fn rt_file_lock(path: text) -> bool
extern fn rt_file_unlock(path: text) -> bool
extern fn rt_file_read_at(path: text, offset: i64, len: i64) -> text
extern fn rt_file_write_at(path: text, offset: i64, data: text) -> bool
extern fn rt_dir_scan(path: text) -> [text]
```

**TODOs addressed:**
- #20: Windows timeout implementation
- #21: Resource limits
- #162-163: Offset file operations
- #102, #377: Directory scanning

### 1.4 Type Conversion Primitives (8 TODOs) ⚪ PRIORITY 4

**Files to modify:**
- `src/compiler/backend/jit_interpreter.spl` - Type conversions (TODOs #50-53)
- `src/compiler/mir_interpreter.spl` - Float conversions (TODOs #123-124)

**TODOs addressed:**
- #50-51: Full Simple type to RuntimeValue conversion
- #52-53: Float/return type handling
- #123-124: Float to/from bits conversion

### 1.5 Basic Parsers (10 TODOs) ⚪ PRIORITY 5

**Files to modify:**
- `src/compiler/blocks/utils.spl` - Parser integrations (TODOs #68-72)
- `src/compiler/loader/compiler_ffi.spl` - JSON parsing (TODOs #110-112)
- `src/compiler/linker/smf_reader.spl` - SDN parsing (TODO #107)
- `src/compiler/monomorphize/hot_reload.spl` - SDN parsing (TODO #161)
- `src/compiler/driver/incremental.spl` - SDN serialization (TODOs #82-83)

**TODOs addressed:**
- #68, #110-112: JSON parser integration
- #69-72: YAML, TOML, XML, CSV parsers
- #82-83, #107, #161: SDN parser integration

---

## Implementation Order

### Week 1: String & Memory FFI
1. ✅ Day 1-2: Implement 1.1 (String Conversion FFI)
2. ⚪ Day 3-4: Implement 1.2 (Memory Operations FFI)
3. ⚪ Day 5: Test & validate Phase 1.1-1.2

### Week 2: File I/O & Type Conversion
4. ⚪ Day 1-2: Implement 1.3 (File I/O Extensions)
5. ⚪ Day 3-4: Implement 1.4 (Type Conversion Primitives)
6. ⚪ Day 5: Test & validate Phase 1.3-1.4

### Week 3: Parsers & Integration
7. ⚪ Day 1-3: Implement 1.5 (Basic Parsers)
8. ⚪ Day 4-5: Integration testing, Phase 1 complete

---

## Success Criteria for Phase 1

- [ ] All 48 Phase 1 TODOs marked complete
- [ ] Test pass rate increases from 330/330 (100%) to maintain 100%
- [ ] No new test failures introduced
- [ ] FFI functions have unit tests
- [ ] Documentation updated for new FFI functions

---

## Next Phases (Summary)

**Phase 2:** Parser & Lexer Enhancements (52 TODOs)
- Expression parsing, type system integration, error messages
- Dependencies: Phase 1 complete

**Phase 3:** MIR Optimization & Codegen (45 TODOs)
- DCE, inlining, loop opts, code generation
- Dependencies: Phases 1-2 complete

**Phase 4:** Monomorphization & Generics (38 TODOs)
- Template specialization, SMF format, hot reload
- Dependencies: Phases 1-3 complete

**Phase 5:** Module System & Linking (42 TODOs)
- Module resolution, linking, package management
- Dependencies: Phases 1-4 complete

**Phase 6:** Runtime & Backend Infrastructure (68 TODOs)
- Backend implementations, interpreter enhancements
- Dependencies: Phases 1-3 complete

**Phase 7:** Advanced Features & Polish (90 TODOs)
- Compiler integration tests, advanced types, tooling
- Dependencies: All previous phases complete

---

## Total Timeline: 5-6 months

**Current Status:** Phase 1.1 in progress (String Conversion FFI)
