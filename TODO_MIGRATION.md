# Migration TODO List

## CRITICAL - Compiler Team

- [ ] Fix method resolution bug (`self.field.method()` treated as enum)
- [ ] Add static method dispatch for imported types
- [ ] Improve error messages (add line numbers, source context)

## Phase 2: Diagnostics (CURRENT FOCUS)

### Next 1-2 Hours
- [ ] Implement TextFormatter (ANSI colors, source snippets)
- [ ] Implement JsonFormatter (machine-readable output)
- [ ] Implement SimpleFormatter (Simple syntax)

### Next 3-5 Hours
- [ ] Write SSpec tests for diagnostics (75 unit + 19 integration)
- [ ] Create diagnostics_minimal module (no i18n for parser)
- [ ] Test in 3 modes (interpreter, SMF, native)

### Later
- [ ] Integrate with i18n FFI
- [ ] Performance benchmarking
- [ ] Documentation completion

## Phase 1: SDN (BLOCKED - Waiting for Compiler Fix)

- [ ] Test SDN CLI commands (check, get, to-json)
- [ ] Migrate simple/std_lib/src/db.spl
- [ ] Migrate simple/std_lib/src/config.spl
- [ ] Delete Rust FFI files
- [ ] Integration testing
- [ ] Performance validation

## Phase 3: Dependency Tracker (PLANNING)

- [ ] Review Lean proofs (17 theorems)
- [ ] Design Simple data structures
- [ ] Plan graph algorithm implementations
- [ ] Create SSpec test framework
- [ ] Begin implementation (10 weeks estimated)

---

Last Updated: 2026-01-30
