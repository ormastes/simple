# Windows C compiler selection lint rule

## Contract

`windows_c_compiler_selection` is the production static-lint rule registered in
`src/compiler/90.tools/lint/static_rules.spl`. It emits deny finding
`W-WIN-CC-001` when a Windows compiler-selection setting violates the MSVC ABI
policy.

The admitted C drivers are LLVM 23.1.x `clang-cl.exe` and `clang.exe` reached
through a validated official Windows LLVM distribution. The default root is
`C:/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc`; a relocated root such
as the PR1216 CI workspace cache is also admitted when the same source includes
a root-bound driver, an executed version query, an exact 23.1.x predicate, and
a fail-closed error path.

## Cases in the executable SSpec

| Selection or input | Expected result |
| --- | --- |
| `CC=gcc`, `export CC=gcc`, PowerShell `$env:CC`, batch `set`, YAML `CC:`, and `GITHUB_ENV` assignments | deny `W-WIN-CC-001` |
| target-qualified `CC_x86_64_pc_windows_msvc`, legacy `cl`, `clang++`, or `CXX` | deny `W-WIN-CC-001` |
| Windows GNU Cargo target or MinGW/GCC driver under that target | deny `W-WIN-CC-001` |
| LLVM 23.1.x `clang-cl.exe` under the default local root with a fail-closed exact version predicate | no finding |
| PR1216 CI workspace root and another relocated official 23.1.x root with root-bound driver, exact predicate, and attestation | no finding |
| Unknown alias, missing version validation, or a bare `--version` token | deny `W-WIN-CC-001` |
| Cargo MSVC `linker = "link.exe"` | no finding; this is a Rust linker setting |
| Linux Cargo settings, comments, documentation, vendor files, and Linux paths inside an MSVC-named checkout | no finding |
| Current Windows shell, CMake, and Cargo inputs | no finding |
| Canonical static rule table | includes `windows_c_compiler_selection` |

The executable source is
`test/01_unit/compiler/lint/windows_c_compiler_selection_spec.spl`.

## Execution and generated-document state

- Generated specification document: pending.
- Self-hosted SSpec execution: pending because the isolated review worktree has
  no self-hosted runner available.
- No pass or fail result is claimed here. The Rust seed fallback is prohibited
  for this check.
