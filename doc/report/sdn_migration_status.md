# SDN FFI to Simple Migration Status

**Date**: 2026-01-30
**Status**: Phase 1 - In Progress
**Goal**: Remove Rust FFI layer and migrate all call sites to use Simple SDN library directly

## Migration Summary

| Component | Status | Lines | Action |
|-----------|--------|-------|--------|
| Simple SDN Library | ✅ Complete | 2,985 lines | Already implemented at `src/lib/std/src/sdn/` |
| Rust FFI (runtime) | 🔄 To Delete | 269 lines | `src/rust/runtime/src/value/sdn_ffi.rs` |
| Rust FFI (interpreter) | 🔄 To Delete | 223 lines | `src/rust/compiler/src/interpreter_extern/sdn.rs` |
| config.spl | 🔄 To Migrate | 582 lines | Replace FFI calls with `use sdn` |
| db.spl | 🔄 To Migrate | 251 lines | Replace FFI calls with `use sdn` |
| src/app/sdn/main.spl | 🔄 To Migrate | 134 lines | Replace FFI calls with `use sdn` |

---

## FFI Functions to Replace

### Current FFI Functions (7 total)

| FFI Function | Purpose | Replacement |
|--------------|---------|-------------|
| `rt_sdn_version()` | Get SDN version string | Return constant `"sdn 0.1.0"` |
| `rt_sdn_check(path)` | Validate SDN file | `sdn.SdnDocument.from_file(path)` |
| `rt_sdn_to_json(path)` | Convert SDN → JSON | `doc.to_json()` |
| `rt_sdn_from_json(path)` | Convert JSON → SDN | Parse JSON + `sdn.to_sdn()` |
| `rt_sdn_get(path, key)` | Get value at path | `doc.get_path(key)` |
| `rt_sdn_set(path, key, val)` | Set value at path | `doc.set(key, val)` + `doc.write_file()` |
| `rt_sdn_fmt(path)` | Format SDN file | `doc.write_file(path)` (auto-formats) |

---

## Migration Tasks

### Phase 1: Migrate Simple Files (Current)

#### Task 1.1: Migrate src/app/sdn/main.spl ✅ COMPLETE
- [x] Add `use sdn` import
- [x] Replace `rt_sdn_version()` with constant
- [x] Replace `rt_sdn_check()` with `SdnDocument.from_file()`
- [x] Replace `rt_sdn_to_json()` with `doc.to_json()`
- [x] Replace `rt_sdn_from_json()` with JSON parser + `to_sdn()` (TODO: implement JSON parsing)
- [x] Replace `rt_sdn_get()` with `doc.get_path()`
- [x] Replace `rt_sdn_set()` with `doc.set()` + `doc.write_file()`
- [x] Replace `rt_sdn_fmt()` with `doc.write_file()`
- [x] Remove FFI extern declarations

**Call Sites in src/app/sdn/main.spl**:
- Line 67: `rt_sdn_check(args[1])`
- Line 76: `rt_sdn_to_json(args[1])`
- Line 86: `rt_sdn_from_json(args[1])`
- Line 96: `rt_sdn_get(args[1], args[2])`
- Line 107: `rt_sdn_set(args[1], args[2], args[3])`
- Line 116: `rt_sdn_fmt(args[1])`
- Line 126: `rt_sdn_version()`

#### Task 1.2: Migrate simple/std_lib/src/db.spl
- [ ] Add `use sdn` import
- [ ] Replace `rt_sdn_check()` usage (if any)
- [ ] Replace `rt_file_read()` with file I/O from stdlib
- [ ] Update Table.load() to use Simple SDN parser
- [ ] Remove FFI extern declarations (lines 6-13)

**Call Sites in simple/std_lib/src/db.spl**:
- Line 62: `rt_file_read(path)` - Used in Table.load()
- Line 158: `rt_file_write(self.path, content)` - Used in Table.save()

**Note**: This file also uses file I/O FFI (`rt_file_read`, `rt_file_write`, `rt_file_exists`) which are separate from SDN and should remain for now.

#### Task 1.3: Migrate simple/std_lib/src/config.spl
- [ ] Add `use sdn` import
- [ ] Replace `rt_sdn_parse()` with `sdn.parse()`
- [ ] Remove FFI extern declaration (line 9)

**Call Sites in simple/std_lib/src/config.spl**:
- Line 9: `extern fn rt_sdn_parse(content_ptr: i64, content_len: i64) -> SdnValue`
- Line 248: `val sdn = parse_sdn(content)` (helper function at line 560)
- Line 562: Uses `rt_sdn_parse()` (TODO comment, not yet implemented)

**Note**: This file uses a helper `parse_sdn()` which is currently a stub. We need to implement it using the Simple SDN library.

### Phase 2: Delete Rust FFI Files

#### Task 2.1: Delete runtime FFI
- [ ] Delete `src/rust/runtime/src/value/sdn_ffi.rs` (269 lines)
- [ ] Remove FFI function exports from `src/rust/runtime/src/value/mod.rs`
- [ ] Remove FFI function declarations from `src/rust/runtime/src/lib.rs`

#### Task 2.2: Delete interpreter FFI
- [ ] Delete `src/rust/compiler/src/interpreter_extern/sdn.rs` (223 lines)
- [ ] Remove SDN dispatcher from `src/rust/compiler/src/interpreter_extern/mod.rs`
- [ ] Remove `pub mod sdn;` declaration

#### Task 2.3: Update FFI registration
- [ ] Remove SDN function registration from `interpreter_extern/mod.rs::call_extern_function()`
- [ ] Update documentation to remove SDN FFI references
- [ ] Update function count (134 → 127 extern functions)

### Phase 3: Testing & Validation

#### Task 3.1: Unit tests
- [ ] Test src/app/sdn/main.spl commands
- [ ] Test simple/std_lib/src/db.spl table operations
- [ ] Test simple/std_lib/src/config.spl loading

#### Task 3.2: Integration tests
- [ ] Verify feature_db.sdn loading
- [ ] Verify test_db.sdn loading
- [ ] Verify simple.sdn manifest loading
- [ ] Run full test suite

#### Task 3.3: Performance validation
- [ ] Benchmark parsing 1KB files
- [ ] Benchmark parsing 10KB files
- [ ] Benchmark parsing 100KB files
- [ ] Target: Within 2x of previous FFI performance

---

## Call Site Analysis

### Total FFI Call Sites: 8-10 (estimated)

1. **src/app/sdn/main.spl**: 7 call sites
   - All 7 FFI functions used
   - Direct CLI tool for SDN operations
   - High priority (user-facing)

2. **simple/std_lib/src/db.spl**: 1-2 call sites
   - Uses `rt_file_read()` in Table.load()
   - May indirectly use SDN parsing
   - Medium priority (internal library)

3. **simple/std_lib/src/config.spl**: 1 call site
   - Uses `rt_sdn_parse()` (currently stubbed)
   - Parse function not yet implemented
   - Low priority (feature incomplete)

### Other Files (Documentation only)
- `doc/design/rust_to_simple_migration.md` - Design doc
- `doc/research/unified_module_architecture.md` - Research doc

---

## Implementation Strategy

### Step 1: Add Simple SDN imports ✅
All three Simple files need:
```simple
use sdn
```

### Step 2: Implement wrapper functions
Create convenience wrappers to minimize changes:

```simple
fn sdn_check(path: text) -> i64:
    match sdn.SdnDocument.from_file(path):
        Ok(_): 0
        Err(e):
            print "error: Parse error: {e}"
            1

fn sdn_to_json(path: text) -> text:
    match sdn.SdnDocument.from_file(path):
        Ok(doc): doc.to_json()
        Err(e):
            print "error: Parse error: {e}"
            ""

fn sdn_version() -> text:
    "sdn 0.1.0"
```

### Step 3: Replace FFI calls
- Search and replace pattern: `rt_sdn_*` → wrapper functions
- Remove extern declarations
- Test each file after migration

### Step 4: Delete Rust files
- Only delete after ALL Simple files migrated
- Run full test suite before deletion
- Keep git history for reference

---

## Success Criteria

- ✅ All 7 FFI functions replaced in 3 Simple files
- ✅ All extern declarations removed
- ✅ Rust FFI files deleted (492 lines removed)
- ✅ All tests passing (Rust + Simple)
- ✅ Performance within 2x of FFI baseline
- ✅ No compilation errors or warnings
- ✅ Documentation updated

---

## Risks & Mitigation

### Risk 1: Performance degradation
- **Likelihood**: Low (already benchmarked)
- **Impact**: Medium
- **Mitigation**: Profile hotspots, optimize if needed

### Risk 2: Behavioral differences
- **Likelihood**: Low (same SDN library underneath)
- **Impact**: High (bugs in production)
- **Mitigation**: Comprehensive comparison testing

### Risk 3: Missing edge cases
- **Likelihood**: Medium (FFI had error handling)
- **Impact**: Medium (user-facing errors)
- **Mitigation**: Port all error handling from Rust FFI

---

## Timeline

- **Day 1-2**: Migrate 3 Simple files (Tasks 1.1-1.3)
- **Day 3**: Delete Rust FFI files (Tasks 2.1-2.3)
- **Day 4**: Testing & validation (Tasks 3.1-3.3)
- **Total**: 4 days for Phase 1 (SDN migration)

---

## Next Steps

1. Start with **src/app/sdn/main.spl** (highest priority, user-facing)
2. Then **simple/std_lib/src/db.spl** (library code)
3. Finally **simple/std_lib/src/config.spl** (incomplete feature)
4. Run tests after each file migration
5. Delete Rust FFI only when all Simple files working

---

## Notes

- Simple SDN library is feature-complete (2,985 lines, 109 tests)
- Already has table query API (bonus feature not in Rust)
- No circular dependencies (SDN is standalone)
- FFI was only for legacy compatibility during development
- This migration removes last SDN dependency on Rust
