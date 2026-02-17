# Feature Test Index

Generated: 2026-02-17

Tracks all test files for the 9 active features across unit, feature, and system test tiers.

---

## Coverage by Feature

| Feature | Unit Tests | Feature Tests | System Tests | Total |
|---------|-----------|---------------|--------------|-------|
| F1: BackendPort Typed Composition Root | 19 | 35 | 16 | 70 |
| F2: Pipeline Stage Ports (CompilerServices) | 61 | 43 | 31 | 135 |
| F3: Default Field Values in Structs | 14 | — | 17 | 31 |
| F4: Trait Desugar (trait-to-struct transform) | 18 | — | — | 18 |
| F5: DI Extension Container | 46 | 31 | 10 | 87 |
| F6: Structural Subtyping | 7 | — | 11 | 18 |
| F7: Implicit Context Parameters | 14 | 8 | 12 | 34 |
| F8: Architecture Check (`check-arch` command) | 44 | — | — | 44 |
| F9: DI System Test Lock | 72 | 60 | 16 | 148 |
| **Total** | **295** | **177** | **113** | **585** |

Notes:
- F9 unit count includes both `di_lock_spec.spl` (14), `di_lock_phases_spec.spl` (29), and shared coverage via `extensions_phases_spec.spl` lock section; feature count includes `di_lock_feature_spec.spl` (29) and `di_lock_all_phases_spec.spl` (31).
- F5 unit count includes `extensions_spec.spl` (14) and `extensions_phases_spec.spl` (32).
- F2 unit count includes `compiler_services_spec.spl` (29) and `compiler_services_phases_spec.spl` (32).
- System tests for F1, F2, F5, F9 share `di_composition_system_spec.spl` (16 tests).

---

## Feature 1: BackendPort Typed Composition Root

Replaces `di.resolve("Backend")` (string-keyed, untyped) with a typed `BackendPort` struct on `CompilerServices`.
Design: `doc/research/di_composition_root_design.md` Option A.
Source: `src/compiler/backend_port.spl`.

### Unit Tests

- `test/unit/compiler/backend_port_phases_spec.spl` — 19 tests
  - Phase 1: Basic API — struct construction, field presence, fn-field invocation (7 tests)
  - Phase 2: Integration — BackendPort embedded in CompilerServices, custom backend construction (6 tests)
  - Phase 3: System behavior — typed contract, identity consistency, edge cases (6 tests)

### Feature Tests

- `test/feature/backend_port_feature_spec.spl` — 35 tests
  - Phase 1: Struct shape — name field, run_fn field presence (2 tests)
  - Phase 2: Factory creation — noop backend, custom fn-fields (tests)
  - Phase 3: Integration with CompilerServices — backend wired, ports independent
  - Phase 4: Type safety — name uniqueness, backend identification

### System Tests

- `test/system/backend_port_system_spec.spl` — 16 tests
  - End-to-end backend selection, interpreter backend services, fn-fields independently invocable
- `test/system/di_composition_system_spec.spl` — 16 tests (shared with F2, F5, F9)
  - Integration of all four DI features working together

---

## Feature 2: Pipeline Stage Ports (CompilerServices)

`CompilerServices` struct with 9 typed port fields and `create_default_services()` factory.
Design: `doc/report/compiler_mdsoc_impl_plan.md` Phase 2.
Source: `src/compiler/compiler_services.spl`.

### Unit Tests

- `test/unit/compiler/compiler_services_spec.spl` — 29 tests
  - Test Group 1: Factory creates all 9 port fields with correct names (10 tests)
  - Test Group 2: Port fn-fields are callable (10 tests)
  - Test Group 3: Services container has all 9 fields (9 tests)
- `test/unit/compiler/compiler_services_phases_spec.spl` — 32 tests
  - Phase 1: Basic API — all 9 ports, fn-field callability (17 tests)
  - Phase 2: Integration — pipeline stage separation, logger 4-fn port, independent instances (10 tests)
  - Phase 3: System behavior — desugar pass-through, module loader resolve, backend consistency (5 tests)

### Feature Tests

- `test/feature/compiler_services_feature_spec.spl` — 43 tests
  - Phase 1: All 9 ports present with correct names
  - Phase 2: Fn-fields callable and correct behavior
  - Phase 3: Port independence and pipeline composition
  - Phase 4: Factory produces consistent containers

### System Tests

- `test/system/compiler_services_system_spec.spl` — 31 tests
  - End-to-end: all 9 ports accessible and functional
  - Pipeline coordination between lexer, parser, desugarer ports
  - Multiple service container instances independence
- `test/system/di_composition_system_spec.spl` — 16 tests (shared with F1, F5, F9)

---

## Feature 3: Default Field Values in Structs

`field: Type = expr` in struct/class bodies; omitted fields use their declared default.
Implementation: core runtime (`parser.spl` + `ast.spl` + `eval.spl`). No desugar pass needed.

### Unit Tests

- `test/unit/app/desugar/struct_defaults_spec.spl` — 14 tests
  - Verifies desugar pipeline passes structs with defaults through unchanged
  - Integer default, multiple defaults, text default, bool default, expression default (5 test groups)

### Feature Tests

None — feature is fully handled at the core runtime level; no desugar feature spec exists.

### System Tests

- `test/system/struct_defaults_system_spec.spl` — 17 tests
  - Phase 1: Parser supports default syntax (3 tests)
  - Phase 2: Constructor omits defaulted fields (4 tests)
  - Phase 3: Mixed required and defaulted fields (3 tests)
  - Phase 4: Expression defaults and overriding (4 tests)
  - Phase 5: Class-level defaults (3 tests)

---

## Feature 4: Trait Desugar (Trait-to-Struct Transform)

`trait Name: fn method()` desugars to `struct Name: method_fn: fn() -> R`.
`impl TraitName for value:` desugars to a factory function.
Source: `src/app/desugar/trait_desugar.spl`.

### Unit Tests

- `test/unit/app/desugar/trait_desugar_spec.spl` — 18 tests
  - Basic trait-to-struct conversion: header, fn method, fn with no params, fn with no return (4 tests)
  - `me` method conversion to fn-field (2 tests)
  - Multiple methods conversion (1 test)
  - `impl Trait for value:` factory generation (3 tests)
  - Pass-through of non-trait content (2 tests)
  - Integration with `desugar_source()` pipeline (3 tests)
  - Edge cases (3 tests)

### Feature Tests

TODO — no dedicated feature-level spec exists yet for trait desugar end-to-end.

### System Tests

TODO — no dedicated system-level spec exists yet.

---

## Feature 5: DI Extension Container

`CompileContext.extensions: DiContainer` as a dynamic plugin/extension registry,
separate from the typed core services ports.
Source: `src/compiler/di.spl` (DiContainer).

### Unit Tests

- `test/unit/compiler/extensions_spec.spl` — 14 tests
  - Test Group 1: Basic plugin registration (6 tests)
  - Test Group 2: Lock behavior (4 tests)
  - Test Group 3: Separation of typed fields vs extensions (4 tests)
- `test/unit/compiler/extensions_phases_spec.spl` — 32 tests
  - Phase 1: Basic API — container construction, bind_instance, resolve_or, has (13 tests)
  - Phase 2: Integration — multiple plugins, factory binding, separation from typed backend (10 tests)
  - Phase 3: System behavior — lock protection, resolve_or defaults, edge cases (9 tests)

### Feature Tests

- `test/feature/di_extensions_feature_spec.spl` — 31 tests
  - Phase 1: Basic plugin registration (4 tests)
  - Phase 2: Multiple plugins, factory binding (7 tests)
  - Phase 3: Lock protection of extensions (6 tests)
  - Phase 4: Extensions are cleanly separated from typed ports (5 tests)
  - Phase 5: Full integration (9 tests)

### System Tests

- `test/system/di_extensions_system_spec.spl` — 10 tests
  - End-to-end: extensions container isolated from CompilerServices ports
- `test/system/di_composition_system_spec.spl` — 16 tests (shared with F1, F2, F9)

---

## Feature 6: Structural Subtyping

A struct with all fields of another struct satisfies it without explicit declaration
(Go-style duck typing at the type level). Runtime `type_check_value` enforces structural compatibility.

### Unit Tests

- `test/unit/core/structural_subtyping_spec.spl` — 7 tests
  - Basic compatibility: exact type match, struct with extra fields (2 tests)
  - Fn-field structs: port satisfaction with extended repo (2 tests)
  - Multiple fn-fields (1 test)
  - Struct-in-struct nesting (1 test)
  - Value passing (1 test)

### Feature Tests

None — this feature is exercised via runtime behavior tested at system level.

### System Tests

- `test/system/structural_subtyping_system_spec.spl` — 11 tests
  - Phase 1: Basic compatibility — same fields, field access regardless of type name (2 tests)
  - Phase 2: Fn-field ports — OrderRepoPort, extended repo with extra fields (3 tests)
  - Phase 3: Multiple fn-fields (2 tests)
  - Phase 4: Struct composition (2 tests)
  - Phase 5: Real-world patterns — DI composition, pipeline ports (2 tests)

---

## Feature 7: Implicit Context Parameters

`context val name: Type` declares a module-level context variable.
`with_context(name: value): body` sets the context for a scope.
Desugared to `var __ctx_name: Type = nil` + save/set/restore pattern.
Source: `src/app/desugar/context_params.spl`.

### Unit Tests

- `test/unit/app/desugar/context_params_spec.spl` — 14 tests
  - Basic context declaration: transforms `context val` to `var __ctx_`: (3 tests)
  - Reference replacement: replaces context variable uses with `__ctx_` prefix (4 tests)
  - `with_context` block transformation (3 tests)
  - Multiple context variables (2 tests)
  - Pass-through: non-context source unchanged (2 tests)

### Feature Tests

- `test/feature/implicit_context_spec.spl` — 8 tests
  - Feature 7: Implicit Context Parameters — module-level context var, with_context binding (3 tests)
  - Feature 7: Multiple Context Variables — two context vars independently set (3 tests)
  - Nil-check patterns on context variables (2 tests)

### System Tests

- `test/system/context_params_system_spec.spl` — 12 tests
  - Phase 1: Module-level context variables — nil initial value, assignment, read from function (4 tests)
  - Phase 2: Context as shared state — multiple functions use same context (3 tests)
  - Phase 3: Context isolation patterns — save/restore simulation (3 tests)
  - Phase 4: Two context variables — independent state (2 tests)

---

## Feature 8: Architecture Check (`check-arch` command)

`simple check-arch [root_dir]` scans `__init__.spl` files for `arch {}` blocks with
`imports { allow = [...] deny = [...] }` rules, then validates actual `use` statements.
Source: `src/app/cli/arch_check.spl`.

### Unit Tests

- `test/unit/app/arch_check_spec.spl` — 44 tests
  - `_str_trim`: leading/trailing/both whitespace, empty (5 tests)
  - `_parse_pattern_list`: single, multiple, glob, missing brackets, empty list (5 tests)
  - `_parse_arch_block`: no block, has block, allow patterns, deny patterns, both, no imports block (6 tests)
  - `_module_path_from_init_file`: absolute path, top-level, deeply nested (3 tests)
  - `_parse_imports_from_content`: simple use, multiple use, dot-to-slash, non-use lines, wildcard (5 tests)
  - `_match_pattern`: exact, mismatch, `/**` glob, direct child, sibling, prefix boundary, partial prefix, exact no subpath (8 tests)
  - `_is_import_allowed`: no rules, deny match, deny non-match, allow match, allow non-match, deny precedence, allow with deny exclusion (7 tests)
  - `_file_is_under_module`: under, not under, empty module (3 tests)
  - Implementation existence checks: source file present, wired in main.spl (2 tests)

### Feature Tests

None — `check-arch` is a CLI tool with unit coverage; no feature-level BDD spec exists.

### System Tests

None — integration via CLI tested via unit-level shell invocation in `arch_check_spec.spl`.

---

## Feature 9: DI System Test Lock

`DiContainer` with `lock()`/`unlock()`/`is_locked()`. Locked container rejects new bindings
but resolves existing ones. Env-var lock: `SIMPLE_SYSTEM_TEST=1` activates global lock
(bypassed when `SIMPLE_DI_TEST=1`).
Source: `src/compiler/di.spl`.

### Unit Tests

- `test/unit/compiler/di_lock_spec.spl` — 14 tests
  - Explicit lock: blocks bind, blocks bind factory, allows after unlock, is_locked, resolve while locked (5 tests)
  - Env-var based lock: SIMPLE_SYSTEM_TEST=1 blocks, =0 allows, di_test bypass, is_locked reflects env (4 tests)
  - `di_is_system_test_locked`: no env var, system_test without di_test, di_test allows (3 tests)
  - Locked preserves existing bindings: pre-lock bindings, resolve_or (2 tests)
- `test/unit/compiler/di_lock_phases_spec.spl` — 29 tests
  - Phase 1: Basic API — initial state, lock ops, unlock ops, resolve while locked (10 tests)
  - Phase 2: Integration — lock protects production bindings, di_is_system_test_locked, env-var locking (12 tests)
  - Phase 3: System behavior — lock as system test guard, preserve resolve_or, env-var cleanup (7 tests)

### Feature Tests

- `test/feature/di_lock_feature_spec.spl` — 29 tests
  - Phase 1: Lock state — starts unlocked, lock/unlock transitions, is_locked (4 tests)
  - Phase 2: Locked behavior — bind_instance, bind factory, bind_tagged all blocked (5 tests)
  - Phase 3: Lock semantics — pre-lock bindings resolvable, resolve_or with defaults (5 tests)
  - Phase 4: Integration — multiple bindings, lock-unlock-relock (4 tests)
  - Phase 5: Full system — env-var lock, di_is_system_test_locked, bypass (11 tests)
- `test/feature/di_lock_all_phases_spec.spl` — 31 tests
  - Comprehensive phase coverage with additional edge cases and env-var cleanup scenarios

### System Tests

- `test/system/di_composition_system_spec.spl` — 16 tests (shared with F1, F2, F5)
  - DI lock in full composition context: lock prevents test pollution of production bindings

---

## Running All Feature Tests

```bash
# All feature tests
bin/simple test test/feature/

# All system tests
bin/simple test test/system/

# All unit tests (compiler and app sub-trees)
bin/simple test test/unit/compiler/
bin/simple test test/unit/app/

# Per-feature unit tests
bin/simple test test/unit/compiler/backend_port_phases_spec.spl      # F1
bin/simple test test/unit/compiler/compiler_services_phases_spec.spl # F2
bin/simple test test/unit/app/desugar/struct_defaults_spec.spl       # F3
bin/simple test test/unit/app/desugar/trait_desugar_spec.spl         # F4
bin/simple test test/unit/compiler/extensions_phases_spec.spl        # F5
bin/simple test test/unit/core/structural_subtyping_spec.spl         # F6
bin/simple test test/unit/app/desugar/context_params_spec.spl        # F7
bin/simple test test/unit/app/arch_check_spec.spl                    # F8
bin/simple test test/unit/compiler/di_lock_phases_spec.spl           # F9

# Per-feature feature tests
bin/simple test test/feature/backend_port_feature_spec.spl      # F1
bin/simple test test/feature/compiler_services_feature_spec.spl # F2
bin/simple test test/feature/di_extensions_feature_spec.spl     # F5
bin/simple test test/feature/implicit_context_spec.spl          # F7
bin/simple test test/feature/di_lock_feature_spec.spl           # F9

# Per-feature system tests
bin/simple test test/system/backend_port_system_spec.spl         # F1
bin/simple test test/system/compiler_services_system_spec.spl    # F2
bin/simple test test/system/struct_defaults_system_spec.spl      # F3
bin/simple test test/system/structural_subtyping_system_spec.spl # F6
bin/simple test test/system/context_params_system_spec.spl       # F7
bin/simple test test/system/di_composition_system_spec.spl       # F1+F2+F5+F9
```

---

## Test File Inventory by Feature

### F1: BackendPort

| File | Type | Tests |
|------|------|-------|
| `test/unit/compiler/backend_port_phases_spec.spl` | Unit | 19 |
| `test/feature/backend_port_feature_spec.spl` | Feature | 35 |
| `test/system/backend_port_system_spec.spl` | System | 16 |
| `test/system/di_composition_system_spec.spl` | System (shared) | 16 |

### F2: Pipeline Stage Ports

| File | Type | Tests |
|------|------|-------|
| `test/unit/compiler/compiler_services_spec.spl` | Unit | 29 |
| `test/unit/compiler/compiler_services_phases_spec.spl` | Unit | 32 |
| `test/feature/compiler_services_feature_spec.spl` | Feature | 43 |
| `test/system/compiler_services_system_spec.spl` | System | 31 |
| `test/system/di_composition_system_spec.spl` | System (shared) | 16 |

### F3: Default Field Values

| File | Type | Tests |
|------|------|-------|
| `test/unit/app/desugar/struct_defaults_spec.spl` | Unit | 14 |
| `test/system/struct_defaults_system_spec.spl` | System | 17 |

### F4: Trait Desugar

| File | Type | Tests |
|------|------|-------|
| `test/unit/app/desugar/trait_desugar_spec.spl` | Unit | 18 |
| test/feature/trait_forwarding_spec.spl (Phase 3 forwarding, related) | Feature | 8 |

### F5: DI Extension Container

| File | Type | Tests |
|------|------|-------|
| `test/unit/compiler/extensions_spec.spl` | Unit | 14 |
| `test/unit/compiler/extensions_phases_spec.spl` | Unit | 32 |
| `test/feature/di_extensions_feature_spec.spl` | Feature | 31 |
| `test/system/di_extensions_system_spec.spl` | System | 10 |
| `test/system/di_composition_system_spec.spl` | System (shared) | 16 |

### F6: Structural Subtyping

| File | Type | Tests |
|------|------|-------|
| `test/unit/core/structural_subtyping_spec.spl` | Unit | 7 |
| `test/system/structural_subtyping_system_spec.spl` | System | 11 |

### F7: Implicit Context Parameters

| File | Type | Tests |
|------|------|-------|
| `test/unit/app/desugar/context_params_spec.spl` | Unit | 14 |
| `test/feature/implicit_context_spec.spl` | Feature | 8 |
| `test/system/context_params_system_spec.spl` | System | 12 |

### F8: Architecture Check

| File | Type | Tests |
|------|------|-------|
| `test/unit/app/arch_check_spec.spl` | Unit | 44 |

### F9: DI System Test Lock

| File | Type | Tests |
|------|------|-------|
| `test/unit/compiler/di_lock_spec.spl` | Unit | 14 |
| `test/unit/compiler/di_lock_phases_spec.spl` | Unit | 29 |
| `test/feature/di_lock_feature_spec.spl` | Feature | 29 |
| `test/feature/di_lock_all_phases_spec.spl` | Feature | 31 |
| `test/system/di_composition_system_spec.spl` | System (shared) | 16 |

---

## Related Test Files (Forwarding Sugar — F3/F4 Adjacent)

These test files exercise the alias forwarding features that complement trait desugar (F4)
and are part of the no-inheritance ergonomics work (`doc/research/no_inheritance_ergonomics_2026-02-16.md`):

| File | Phase | Tests |
|------|-------|-------|
| `test/feature/function_alias_spec.spl` | Phase 1 — deprecated `fn name = target` | 10 |
| `test/feature/method_alias_spec.spl` | Phase 2 — `alias fn/me x = field.method` | 7 |
| `test/feature/trait_forwarding_spec.spl` | Phase 3 — `alias Trait = field` runtime delegation | 8 |
| `test/unit/app/desugar/forwarding_spec.spl` | Phases 2-4 desugar unit tests | 15 |
| `test/unit/app/desugar/trait_scanner_spec.spl` | Trait scanner (Phase 3 support) | 9 |

---

## Status Summary

| Feature | Status | Test Files | Notes |
|---------|--------|-----------|-------|
| F1: BackendPort | Complete | 3 (+ 1 shared) | All phases implemented |
| F2: Pipeline Ports | Complete | 4 (+ 1 shared) | All 9 ports wired |
| F3: Default Field Values | Complete | 2 | Core runtime, no desugar needed |
| F4: Trait Desugar | Complete | 1 + 1 adjacent | Feature test TODO |
| F5: DI Extensions | Complete | 4 (+ 1 shared) | Plugin registry separate from typed ports |
| F6: Structural Subtyping | Complete | 2 | Runtime duck-typing enforced |
| F7: Implicit Context | Complete | 3 | Desugar pass complete |
| F8: Architecture Check | Complete | 1 | CLI tool, unit tests only |
| F9: DI System Test Lock | Complete | 4 (+ 1 shared) | Explicit + env-var lock |
