# Windows C authority verification plan

| Requirement | Executable evidence |
|---|---|
| WINCC-001, WINCC-005 | scripts/check/check-windows-msvc-toolchain-contract.shs; real bootstrap environment capture |
| WINCC-002, WINCC-003, WINCC-004 | test/01_unit/compiler/lint/windows_c_compiler_selection_spec.spl; canonical registry lookup |
| WINCC-001, WINCC-002, WINCC-003 | test/01_unit/scripts/windows_msvc_toolchain_contract_spec.spl |
| WINCC-006 | retained prior-source shell failure, candidate shell PASS, C/CMake and Cargo probe logs and paired metrics |

Retain interpreter SSpec and core/MCP admission as pending until the proper self-hosted binary is available. Do not rerun unchanged passing shell/native criteria merely to restate confidence.
