# Script Conversion to Simple Language

**Status:** Planning
**Date:** 2026-01-09
**Goal:** Convert all Python and Bash scripts to Simple language

---

## Current Inventory

### Python Scripts (5 files, 1,556 lines)

| Script | Lines | Purpose | Priority |
|--------|-------|---------|----------|
| migrate_spec_to_spl.py | 389 | Migrate markdown to _spec.spl | High |
| extract_tests_from_spec.py | 351 | Extract tests from markdown | High |
| spec_gen.py | 370 | Generate markdown from _spec.spl | High |
| scaffold_feature_test.py | 193 | Scaffold feature tests | Medium |
| refactor_lowering.py | 253 | Code refactoring tool | Low |

**Total:** 1,556 lines

### Shell Scripts (6 files, 805 lines)

| Script | Lines | Purpose | Priority |
|--------|-------|---------|----------|
| verify_features.sh | 253 | Verify feature status | Medium |
| gen_spec_docs.sh | 198 | Generate spec documentation | Medium |
| verify_doctest.sh | 119 | Verify doctest | Medium |
| complete_mixin_phase1.sh | 116 | Mixin implementation helper | Low |
| test_visibility.sh | 38 | Test visibility rules | Low |
| compare_features.sh | 63 | Compare feature lists | Low |
| jj-wrappers/git.sh | 18 | Git wrapper for JJ | Low |

**Total:** 805 lines

---

## Prerequisites

### 1. Shell API Implementation ✅ Spec Created

**Created:** `tests/specs/shell_api_spec.spl`
- Process execution (shell.run, shell.pipe)
- File operations (file.read_text, file.write_text, file.exists, etc.)
- Directory operations (dir.list, dir.glob, dir.create, dir.remove)
- Path manipulation (path.join, path.basename, path.dirname, path.ext)
- Environment variables (env.get, env.set)

**Status:** Specification complete, needs implementation

### 2. Required Stdlib Features

**String manipulation:**
- ✅ split, strip, replace, starts_with, ends_with, contains
- ✅ regex support (std.regex)
- ⏳ format strings / string interpolation

**Collections:**
- ✅ List operations (map, filter, enumerate, append)
- ✅ Dictionary/Map support
- ⏳ Tuple unpacking

**I/O:**
- ⏳ File reading/writing (via shell.file)
- ⏳ Command execution (via shell.run)
- ✅ Print/output

**System:**
- ⏳ Command line arguments (sys.args)
- ⏳ Exit codes (sys.exit)
- ⏳ Current working directory

---

## Conversion Strategy

### Phase 1: Shell API Implementation

**Tasks:**
1. Implement shell.run() - Execute commands and capture output
2. Implement file operations - read_text, write_text, exists, copy, move
3. Implement directory operations - list, glob, create, remove
4. Implement path operations - join, basename, dirname, ext
5. Implement env operations - get, set

**Estimate:** 2-3 days

### Phase 2: Convert High-Priority Scripts

Convert the 3 main migration/generation tools:

**1. migrate_spec_to_spl.spl** (from migrate_spec_to_spl.py)
- Extract metadata from markdown
- Parse code blocks
- Generate _spec.spl format
- ~400 lines Simple

**2. extract_tests_from_spec.spl** (from extract_tests_from_spec.py)
- Similar to migrate but extract-only
- Keep original as reference
- ~350 lines Simple

**3. spec_gen.spl** (from spec_gen.py)
- Parse _spec.spl docstrings
- Generate formatted markdown
- ~400 lines Simple

**Estimate:** 3-4 days

### Phase 3: Convert Medium-Priority Scripts

Convert verification and documentation scripts:

**1. verify_features.spl** (from verify_features.sh)
- Check feature implementation status
- Report missing features
- ~250 lines Simple

**2. gen_spec_docs.spl** (from gen_spec_docs.sh)
- Generate spec index
- Create documentation structure
- ~200 lines Simple

**3. verify_doctest.spl** (from verify_doctest.sh)
- Run doctest verification
- Report failures
- ~120 lines Simple

**Estimate:** 2-3 days

### Phase 4: Convert Low-Priority Scripts

Convert remaining utility scripts:

- scaffold_feature_test.spl
- refactor_lowering.spl
- complete_mixin_phase1.spl
- test_visibility.spl
- compare_features.spl
- git wrapper

**Estimate:** 2-3 days

---

## Benefits of Conversion

### 1. Single Language
- No Python dependency
- No complex shell scripts
- Consistent syntax and patterns

### 2. Better Tooling
- IDE support (LSP)
- Type checking
- Refactoring tools
- Debugging support

### 3. More Maintainable
- Explicit types
- Better error handling
- Unit testable
- Self-documenting code

### 4. Cross-Platform
- No bash/zsh differences
- No Python version issues
- Works on Windows without WSL

### 5. Dogfooding
- Exercise Simple language features
- Find missing stdlib functions
- Improve error messages
- Test real-world usage

---

## Implementation Plan

### Week 1: Shell API
- [ ] Implement process execution (shell.run)
- [ ] Implement file I/O (file.*)
- [ ] Implement directory operations (dir.*)
- [ ] Implement path operations (path.*)
- [ ] Test all shell API functions

### Week 2-3: High Priority Conversions
- [ ] Convert migrate_spec_to_spl.py → .spl
- [ ] Convert extract_tests_from_spec.py → .spl
- [ ] Convert spec_gen.py → .spl
- [ ] Test all conversions
- [ ] Verify same behavior as Python versions

### Week 3-4: Medium Priority Conversions
- [ ] Convert verify_features.sh → .spl
- [ ] Convert gen_spec_docs.sh → .spl
- [ ] Convert verify_doctest.sh → .spl
- [ ] Test all conversions

### Week 4-5: Low Priority Conversions
- [ ] Convert remaining scripts
- [ ] Clean up and document
- [ ] Update build system to use Simple scripts

---

## Timeline

**Total Estimate:** 4-5 weeks

**Phased Approach:**
- Week 1: Shell API (foundation)
- Weeks 2-3: Core migration tools (high value)
- Weeks 3-4: Verification tools (medium value)
- Weeks 4-5: Utility tools (nice to have)

---

## Success Criteria

1. ✅ Shell API specification complete
2. ⏳ Shell API implemented and tested
3. ⏳ All high-priority scripts converted
4. ⏳ All scripts produce same output as originals
5. ⏳ No Python or Bash dependencies for core workflows
6. ⏳ Documentation updated with new usage

---

## Current Status

**Completed:**
- ✅ Shell API specification (shell_api_spec.spl)
- ✅ Shell API stub implementation (shell.spl)
- ✅ Conversion plan documented

**Next Steps:**
1. Implement shell.run() with FFI to OS
2. Implement file operations with FFI
3. Test shell API with real use cases
4. Convert migrate_spec_to_spl.py as first full script

---

## Notes

**Complexity:** This is a significant undertaking (~2,400 lines to convert)

**Dependencies:** Requires working shell API before scripts can run

**Value:** High - enables dogfooding and removes external dependencies

**Risk:** Low - Python/Bash versions remain as reference implementations

**Recommendation:** Start with shell API, then convert high-priority scripts incrementally

EOF
