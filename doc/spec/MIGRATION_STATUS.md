# Spec Migration Status

**Last Updated:** 2026-01-09  
**Phase:** Planning Complete, Awaiting Execution

See [SPEC_MIGRATION_PLAN.md](../SPEC_MIGRATION_PLAN.md) for full details.

---

## Quick Summary

**Goal:** Move feature specifications from `doc/spec/*.md` to executable `tests/*_spec.spl` files with docstring documentation, keeping only generated/reference files in `doc/spec/`.

**Rationale:**
- Specifications should be testable and executable
- Tight coupling between spec and tests prevents drift
- `doc/spec/` should contain only reference docs and generated specs
- Current tool cannot support comment-only files (needs implementation)

---

## Migration Categories

### ✅ To Migrate (7 files) - COMPLETE

Direct migrations - feature specs with Feature IDs:

- [x] syntax.md (#10-19) → tests/specs/syntax_spec.spl ✅ **DONE 2026-01-09**
- [x] types.md (#20-29) → tests/specs/types_spec.spl ✅ **DONE 2026-01-09**
- [x] type_inference.md (#13) → tests/specs/type_inference_spec.spl ✅ **DONE 2026-01-09**
- [x] async_default.md (#276-285) → tests/specs/async_default_spec.spl ✅ **DONE 2026-01-09**
- [x] suspension_operator.md (#270-275) → tests/specs/suspension_operator_spec.spl ✅ **DONE 2026-01-09**
- [x] capability_effects.md (#880-884) → tests/specs/capability_effects_spec.spl ✅ **DONE 2026-01-09**
- [x] sandboxing.md (#916-923) → tests/specs/sandboxing_spec.spl ✅ **DONE 2026-01-09**

**Migration Results:**
- Total size: 54.6K of specification content
- Code examples: 137 examples extracted and converted to test cases
- All original .md files marked with migration notice

### 📤 To Extract (8 files)

Extract testable scenarios, keep reference doc:

- [ ] functions.md → tests/specs/functions_spec.spl (keep reference)
- [ ] traits.md → tests/specs/traits_spec.spl (keep reference)
- [ ] memory.md → tests/specs/memory_spec.spl (keep reference)
- [ ] modules.md → tests/specs/modules_spec.spl (keep reference)
- [ ] data_structures.md → tests/specs/data_structures_spec.spl (keep reference)
- [ ] concurrency.md → tests/specs/concurrency_spec.spl (keep reference)
- [ ] macro.md → tests/specs/macro_spec.spl (keep reference)
- [ ] metaprogramming.md → tests/specs/metaprogramming_spec.spl (keep reference)

### 📚 Keep As-Is (45+ files)

Reference documentation, tooling, frameworks:

**Indices & References:**
- README.md (main index)
- language.md (legacy index)
- language_enhancement.md (proposals)

**Implementation References:**
- parser/* (6 files) - Parser implementation
- lexer_parser.md - Token types & grammar

**Tooling Specs:**
- tooling/* (5 files) - Formatter, linter, VSCode, MCP, build audit

**Testing Frameworks:**
- testing/* (6 files) - BDD, doctest, mock, property, snapshot, semantic diff

**Domain-Specific:**
- gpu_simd/* (5 files) - GPU compute & SIMD
- graphics_3d/* (7 files) - 3D rendering pipeline
- tui.md - Terminal UI framework
- web.md - Web framework

**Data & I/O:**
- sdn.md - Simple Data Notation format
- ffi_abi.md - FFI & ABI specification
- file_io.md - File I/O operations
- stdlib.md - Standard library organization

**Supporting Systems:**
- primitive_as_obj.md - Primitive type methods
- simple_math.md - Math library
- units.md, units_part1.md, units_part2.md - Unit type system
- invariant.md - Contract & invariant system

---

## Current Status

### ✅ Phase 2 Complete - All Core Specs Migrated (2026-01-09)

**Category A + Category B: 15/15 files complete**

Migration/extraction completed using automated tools:
- `python scripts/migrate_spec_to_spl.py --all` (Category A)
- `python scripts/extract_tests_from_spec.py --all` (Category B)

**Combined Results:**
- 126.6K of specification content migrated/extracted
- 294 code examples extracted and converted to test cases
- All original .md files marked with appropriate notices
- New specs ready for implementation and validation

**File Organization:**
- `tests/specs/` - All 15 executable specification files
- `doc/spec/` - Reference documentation (Category B) and legacy files (Category A)
- `doc/spec/generated/` - Created for future spec-gen output

### 🔄 Phase 3 In Progress - Organization (2026-01-09)

**Completed:**
- ✅ Updated doc/spec/README.md with migration section
- ✅ Created doc/spec/generated/ directory
- ✅ Updated AGENTS.md with Phase 2 completion

**Remaining:**
- ⏳ Update cross-references in remaining documentation
- ⏳ Final review of all migration/extraction notices

---

## Timeline

- **Week 1:** Preparation (verify _spec.spl support, create tools)
- **Week 2-3:** Core migrations (7 direct + 8 extract migrations)
- **Week 4:** Organization (update README, reorganize structure)
- **Week 5:** Spec generator (`simple spec-gen` command)
- **Week 6:** Validation (coverage check, CI integration)

---

## Progress Tracking

### Phase 1: Preparation ✅ COMPLETE
- [x] Verify comment-only .spl support (✅ Working)
- [x] Create migration script: `scripts/migrate_spec_to_spl.py`
- [x] Create _spec.spl template
- [x] Tag all doc/spec/*.md files

### Phase 2: Core Migrations ✅ COMPLETE
**Direct (7):** 7/7 complete ✅ **ALL DONE**
- [x] syntax.md → syntax_spec.spl (8.1K, 21 examples)
- [x] types.md → types_spec.spl (8.1K, 17 examples)
- [x] type_inference.md → type_inference_spec.spl (7.1K, 24 examples)
- [x] async_default.md → async_default_spec.spl (13K, 37 examples)
- [x] suspension_operator.md → suspension_operator_spec.spl (9.1K, 24 examples)
- [x] capability_effects.md → capability_effects_spec.spl (8.5K, 14 examples)
- [x] sandboxing.md → sandboxing_spec.spl (646 bytes, 0 examples)

**Extract (8):** 8/8 complete ✅ **ALL DONE**
- [x] functions.md → functions_spec.spl (10K, 24 examples)
- [x] traits.md → traits_spec.spl (17K, 36 examples)
- [x] memory.md → memory_spec.spl (7.5K, 17 examples)
- [x] modules.md → modules_spec.spl (767 bytes, 0 examples)
- [x] data_structures.md → data_structures_spec.spl (15K, 32 examples)
- [x] concurrency.md → concurrency_spec.spl (11K, 24 examples)
- [x] macro.md → macro_spec.spl (767 bytes, 0 examples)
- [x] metaprogramming.md → metaprogramming_spec.spl (11K, 24 examples)

### Phase 3: Organization 🔄 IN PROGRESS
- [x] Update doc/spec/README.md with new structure
- [x] Add generated/ directory for future spec-gen output
- [x] Update AGENTS.md with Phase 2 completion
- [ ] Update cross-references in remaining docs
- [ ] Final review of migration notices

### Phase 4: Spec Generator ⏳
- [ ] Implement `simple spec-gen` command
- [ ] CI integration
- [ ] Generated spec validation

### Phase 5: Finalization ⏳
- [ ] Verify coverage
- [ ] Update AGENTS.md
- [ ] Update CLAUDE.md
- [ ] Create SPEC_GUIDELINES.md

---

## After Migration

### New Structure

```
doc/spec/
├── generated/              # Auto-generated from _spec.spl
│   ├── syntax.md
│   ├── types.md
│   └── ...
├── parser/                 # Implementation reference
├── tooling/                # Tool specs
├── testing/                # Framework specs
└── [other reference docs]

tests/
├── specs/                  # Executable specifications
│   ├── syntax_spec.spl
│   ├── types_spec.spl
│   └── ...
└── system/                 # Integration tests
    ├── mixin_spec.spl
    └── ...
```

### Usage

**Generate documentation from specs:**
```bash
# Generate all specs
simple spec-gen --all

# Generate specific spec
simple spec-gen --input tests/specs/syntax_spec.spl --output doc/spec/generated/
```

**Run spec tests:**
```bash
# Run all spec tests
make test-specs

# Run specific spec
simple test tests/specs/syntax_spec.spl
```

---

**For Full Plan:** See [../SPEC_MIGRATION_PLAN.md](../SPEC_MIGRATION_PLAN.md)
