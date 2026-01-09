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

### ✅ To Migrate (7 files)

Direct migrations - feature specs with Feature IDs:

- [ ] syntax.md (#10-19) → tests/specs/syntax_spec.spl
- [ ] types.md (#20-29) → tests/specs/types_spec.spl
- [ ] type_inference.md (#13) → tests/specs/type_inference_spec.spl
- [ ] async_default.md (#276-285) → tests/specs/async_default_spec.spl
- [ ] suspension_operator.md (#270-275) → tests/specs/suspension_operator_spec.spl
- [ ] capability_effects.md (#880-884) → tests/specs/capability_effects_spec.spl
- [ ] sandboxing.md (#916-923) → tests/specs/sandboxing_spec.spl

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

### ✅ Comment-Only .spl Files ARE Supported

**Testing Complete (2026-01-09):**
- Created `tests/meta/comment_only_spec.spl` with only `"""..."""` docstrings
- Successfully compiled: `simple compile tests/meta/comment_only_spec.spl`
- Result: Pure-docstring files compile without errors

**Conclusion:** No parser changes needed. Specification files can be pure docstrings.

---

## Timeline

- **Week 1:** Preparation (verify _spec.spl support, create tools)
- **Week 2-3:** Core migrations (7 direct + 8 extract migrations)
- **Week 4:** Organization (update README, reorganize structure)
- **Week 5:** Spec generator (`simple spec-gen` command)
- **Week 6:** Validation (coverage check, CI integration)

---

## Progress Tracking

### Phase 1: Preparation ✅ (Partial)
- [x] Verify comment-only .spl support (✅ Working)
- [ ] Create migration script: `scripts/migrate_spec_to_spl.py`
- [ ] Create _spec.spl template
- [ ] Tag all doc/spec/*.md files

### Phase 2: Core Migrations ⏳
**Direct (7):** 0/7 complete  
**Extract (8):** 0/8 complete

### Phase 3: Organization ⏳
- [ ] Update doc/spec/README.md
- [ ] Reorganize doc/spec/ structure
- [ ] Update cross-references

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
