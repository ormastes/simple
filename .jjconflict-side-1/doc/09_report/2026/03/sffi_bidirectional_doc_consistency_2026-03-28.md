# SFFI Bidirectional Doc Consistency Report

**Date:** 2026-03-28
**Scope:** Cross-reference, REQ-ID, terminology, and test coverage audit for the SFFI Bidirectional Class Interop feature documentation suite.

> Historical note: this audit reflects the 2026-03-28 document state before the phase-4/plugin-manifest completion work. The current implementation status and reconciled verification state are recorded in `doc/09_report/2026/03/sffi_bidirectional_interop_completion_2026-03-30.md`.

---

## 1. Documents Reviewed

| # | Document | Path |
|---|----------|------|
| 1 | Plan | `/.claude/plans/parsed-questing-goose.md` |
| 2 | Requirements | `doc/02_requirements/feature/usage/sffi_bidirectional_interop.md` |
| 3 | NFR | `doc/02_requirements/nfr/sffi_bidirectional_interop.md` |
| 4 | Architecture | `doc/04_architecture/sffi_bidirectional_interop.md` |
| 5 | Design | `doc/05_design/sffi_bidirectional_interop.md` |
| 6 | System Test | `test/system/sffi_bidirectional_interop_spec.spl` |
| 7 | (related) SFFI External Lib Pattern | `doc/05_design/sffi_external_library_pattern.md` |
| 8 | (related) C++ Wrapper Generator | `doc/05_design/cpp_wrapper_generator_design.md` |

---

## 2. Cross-Reference Status

### 2.1 Link Matrix (before fixes)

| Source -> Target | Plan | Req | NFR | Arch | Design | Test |
|------------------|------|-----|-----|------|--------|------|
| **Plan** | -- | NO | NO | NO | NO | NO |
| **Req** | YES | -- | YES | NO | YES (via related) | NO |
| **NFR** | NO | YES | -- | NO | NO | NO |
| **Arch** | NO | YES | YES | -- | YES | NO |
| **Design** | NO | YES | YES | YES | -- | NO |
| **Test** | NO | NO | NO | NO | YES (partial) | -- |

### 2.2 Issues Found

| ID | Severity | Document | Issue | Fix |
|----|----------|----------|-------|-----|
| XR-01 | ERROR | System Test | References `doc/03_plan/sffi_bidirectional_interop.md` which does NOT exist | Changed to `/.claude/plans/parsed-questing-goose.md` |
| XR-02 | ERROR | System Test | `Requirements` header says `N/A` instead of linking to requirements doc | Fixed to reference the requirements doc |
| XR-03 | WARNING | System Test | `Research` header says `N/A` | Acceptable -- no dedicated research doc for this feature |
| XR-04 | WARNING | System Test | Missing link to architecture doc | Added link |
| XR-05 | WARNING | NFR | Missing links to architecture and design docs | Added links |
| XR-06 | WARNING | Plan | No forward links to any downstream docs (req, arch, design) | Not fixed -- plan is in `.claude/plans/` and is upstream-only by convention |
| XR-07 | INFO | Requirements | Plan link uses absolute root path `/.claude/plans/...` | Acceptable for plans stored outside doc tree |
| XR-08 | WARNING | Design | No link back to the plan | Added link |

### 2.3 Link Matrix (after fixes)

| Source -> Target | Plan | Req | NFR | Arch | Design | Test |
|------------------|------|-----|-----|------|--------|------|
| **Plan** | -- | NO | NO | NO | NO | NO |
| **Req** | YES | -- | YES | NO | YES | NO |
| **NFR** | NO | YES | -- | YES | YES | NO |
| **Arch** | NO | YES | YES | -- | YES | NO |
| **Design** | YES | YES | YES | YES | -- | NO |
| **Test** | YES | YES | NO | NO | YES | -- |

---

## 3. REQ-ID Consistency

### 3.1 Functional Requirements (REQ-SFFI-BIDIR001 through 012)

All 12 requirement IDs are defined in the requirements document and referenced consistently:

| REQ-ID | Req Doc | NFR Doc | Arch Doc | Design Doc | Test |
|--------|---------|---------|----------|------------|------|
| BIDIR001 | DEFINED | via NFR-003,004 | YES | YES (A1) | YES (attribute parsing, validation) |
| BIDIR002 | DEFINED | via NFR-003 | YES | YES (A3,A4) | YES (C ABI generation) |
| BIDIR003 | DEFINED | via NFR-001 | YES | YES (A5) | YES (C header) |
| BIDIR004 | DEFINED | via NFR-001 | YES | YES (A5) | YES (C++ wrapper) |
| BIDIR005 | DEFINED | via NFR-002,003 | YES | YES (implied in layout) | YES (@repr(C) layout) |
| BIDIR006 | DEFINED | via NFR-002,004 | YES | YES (A5 layout_verifier) | YES (_Static_assert) |
| BIDIR007 | DEFINED | via NFR-004 | YES | YES (5.2 SFFI Lint) | YES (SFFI001-005) |
| BIDIR008 | DEFINED | via NFR-001 | YES | YES (A6) | YES (shared lib build) |
| BIDIR009 | DEFINED | via NFR-001 | YES | YES (A6) | PARTIAL (init/shutdown only) |
| BIDIR010 | DEFINED | via NFR-002,004 | YES | YES (implied) | YES (bitfield) |
| BIDIR011 | DEFINED | via NFR-001,004 | YES | NO (Direction B not detailed in design) | **NO** |
| BIDIR012 | DEFINED | -- | YES | YES (A1) | YES (standalone fn) |

### 3.2 Issues Found

| ID | Severity | Issue |
|----|----------|-------|
| REQ-01 | WARNING | REQ-SFFI-BIDIR011 (Plugin Manifest) has no test coverage in system test. This is P2 priority so acceptable for now. |
| REQ-02 | INFO | REQ-SFFI-BIDIR009 acceptance criteria 2-7 (idempotent init, auto-init, etc.) not individually tested. Current test covers basic presence only. |
| REQ-03 | INFO | REQ-SFFI-BIDIR011 has no corresponding design section. The design doc focuses on Direction A (export) and Direction C (layout). Direction B is deferred. |

### 3.3 Non-Functional Requirements (NFR-SFFI-001 through 004)

| NFR-ID | NFR Doc | Arch Doc | Design Doc |
|--------|---------|----------|------------|
| NFR-SFFI-001 (Cross-Platform) | DEFINED | YES (Section 6.1) | YES (A6 linker) |
| NFR-SFFI-002 (ABI Stability) | DEFINED | YES (Section 6.2) | YES (layout verifier) |
| NFR-SFFI-003 (Zero Overhead) | DEFINED | YES (Section 6.2 opaque handle) | YES (A3 wrapper pattern) |
| NFR-SFFI-004 (Compile-Time Safety) | DEFINED | YES (Section 6.2) | YES (A1 validation, lint) |

No NFR-ID inconsistencies found.

---

## 4. Terminology Consistency

| Term | Plan | Req | NFR | Arch | Design | Test | Status |
|------|------|-----|-----|------|--------|------|--------|
| opaque handle | YES | YES | YES | YES | YES | YES | CONSISTENT |
| `spl_Calculator_t` | YES | YES | -- | YES | YES | YES | CONSISTENT |
| `@export("C")` | YES | YES | -- | YES | YES | YES | CONSISTENT |
| `@repr("C")` | YES | YES | -- | YES | YES | YES | CONSISTENT |
| `@bits(N)` | YES | YES | -- | YES | YES (implied) | YES | CONSISTENT |
| opaque handle typedef pattern | `spl_Calculator*` | `spl_Calculator*` | -- | `spl_Calculator*` | **`spl_Calculator_opaque*`** (A4.2) | `spl_Calculator*` | **INCONSISTENT** |
| "three-tier SFFI" | YES | -- | -- | YES | YES | -- | CONSISTENT |
| Direction A/B/C labels | YES | YES | -- | YES | YES | YES | CONSISTENT |

### 4.1 Issues Found

| ID | Severity | Issue | Fix |
|----|----------|-------|-----|
| TERM-01 | WARNING | Design doc section A4.2 uses `spl_Calculator_opaque*` as the typedef struct name, while all other docs use `spl_Calculator*`. The `_opaque` suffix is inconsistent. | Fixed in design doc to use `spl_Calculator*` |

---

## 5. Test Coverage Gaps

| Requirement | Test Present | Test Adequate | Gap |
|-------------|-------------|---------------|-----|
| BIDIR001 | YES (3 parse tests, 3 validation tests) | YES | -- |
| BIDIR002 | YES (4 tests) | YES | -- |
| BIDIR003 | YES (4 tests) | YES | -- |
| BIDIR004 | YES (3 tests) | YES | -- |
| BIDIR005 | YES (3 tests) | YES | -- |
| BIDIR006 | YES (via _Static_assert test in C header) | PARTIAL | No test for C11 vs C++11 assert variant |
| BIDIR007 | YES (5 tests, one per rule) | YES | -- |
| BIDIR008 | YES (3 tests) | YES | -- |
| BIDIR009 | PARTIAL (init/shutdown presence) | NO | Missing: idempotent init, auto-init, shutdown safety |
| BIDIR010 | YES (2 tests) | YES | -- |
| BIDIR011 | **NO** | **NO** | **No plugin manifest tests at all** |
| BIDIR012 | YES (1 test in parse section) | YES | -- |

### Recommendations

1. **Add REQ-SFFI-BIDIR011 tests** when Direction B implementation begins (P2 priority, acceptable to defer).
2. **Expand REQ-SFFI-BIDIR009 tests** to cover idempotent init, safe double-shutdown, and auto-init flag.
3. **Add REQ-SFFI-BIDIR006 test** for `static_assert` (C++11) variant in `.hpp` headers.

---

## 6. Conflict Check with Related Documents

### 6.1 sffi_external_library_pattern.md

- Describes the 3-tier SFFI pattern for C++ -> Simple (Direction B in bidirectional doc).
- **No conflicts.** The bidirectional doc's Direction B explicitly references and builds upon this pattern.
- The bidirectional doc adds the plugin manifest (REQ-SFFI-BIDIR011) to unblock the semantic analyzer, which is the documented blocker in the external library pattern.

### 6.2 cpp_wrapper_generator_design.md

- Describes automatic wrapper generation tooling for the 3-tier pattern.
- **No conflicts.** The wrapper generator is a tooling concern orthogonal to the bidirectional interop feature.
- Both docs reference the same source files (`src/app/wrapper_gen/`).

### 6.3 phase4_sffi_implementation_plan.md

- Referenced by the plan and requirements docs.
- **Consistent.** Both identify the semantic analyzer rejection of unregistered `extern fn` as the key blocker.

---

## 7. Fixes Applied

| Fix ID | File | Change |
|--------|------|--------|
| FIX-01 | `test/system/sffi_bidirectional_interop_spec.spl` | Changed `Plan:` from nonexistent path to correct plan path |
| FIX-02 | `test/system/sffi_bidirectional_interop_spec.spl` | Changed `Requirements:` from `N/A` to actual requirements doc path |
| FIX-03 | `test/system/sffi_bidirectional_interop_spec.spl` | Added `Architecture:` link |
| FIX-04 | `doc/02_requirements/nfr/sffi_bidirectional_interop.md` | Added links to architecture and design docs |
| FIX-05 | `doc/05_design/sffi_bidirectional_interop.md` | Added link to plan |
| FIX-06 | `doc/05_design/sffi_bidirectional_interop.md` | Changed `spl_Calculator_opaque*` to `spl_Calculator*` for consistency |

---

## 8. Summary

| Category | Total Issues | Errors | Warnings | Info |
|----------|-------------|--------|----------|------|
| Cross-references | 8 | 2 | 4 | 2 |
| REQ-ID consistency | 3 | 0 | 1 | 2 |
| Terminology | 1 | 0 | 1 | 0 |
| Test coverage | 3 gaps | 0 | 2 | 1 |
| Conflicts | 0 | 0 | 0 | 0 |
| **Total** | **15** | **2** | **8** | **5** |

All 2 errors have been fixed. 1 of 8 warnings fixed (TERM-01). The remaining warnings are acceptable deferrals (plan links, test gaps for P2/P3 features).
