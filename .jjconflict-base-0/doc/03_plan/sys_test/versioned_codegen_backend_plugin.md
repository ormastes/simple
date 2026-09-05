# Versioned backend plugin system-test plan

<!-- codex-design -->

| Requirement | Scenario |
|---|---|
| REQ-001/008 | Both providers compile through `BackendSession`; structural gate rejects direct caller access |
| REQ-002/006 | Built-in and dynamic descriptors admit; bad symbol/ABI/MIR digest fail closed |
| REQ-003 | Interpreter defaults Cranelift and explicitly selects LLVM |
| REQ-004 | Compiler defaults LLVM and explicitly selects Cranelift |
| REQ-005/007 | One loader selects deterministically; unavailable selection never substitutes |
| REQ-009 | Provider identity changes invalidate receipt/cache reuse |
| REQ-010 | Existing built-in outputs remain behaviorally equivalent during migration |

Planned executable:
`test/03_system/app/compiler/feature/versioned_codegen_backend_plugin_spec.spl`.
Manual helpers: `step("select backend for execution role")`,
`step("admit versioned provider")`, `step("compile through backend session")`,
and `step("reject incompatible provider without fallback")`. Setup helper:
`prepare_backend_plugin_fixture`. Checkers:
`check_admission_receipt`, `check_selected_provider`, and
`check_no_backend_substitution`. Any unavailable provider fixture uses
`fail("backend provider fixture unavailable")`, never a placeholder pass.

