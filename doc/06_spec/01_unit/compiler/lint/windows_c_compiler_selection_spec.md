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
| raw, exported, or batch target-qualified `CC_x86_64_pc_windows_msvc`/`CXX_x86_64_pc_windows_msvc`, legacy `cl`, `clang++`, or `CXX` | deny `W-WIN-CC-001` |
| Windows GNU Cargo target or MinGW/GCC driver under that target | deny `W-WIN-CC-001` |
| LLVM 23.1.x `clang-cl.exe` under the default local root with a fail-closed exact version predicate | no finding |
| PR1216 CI workspace root with its clang-cl pattern mapping, and another relocated official 23.1.x root with a direct exact predicate | no finding |
| Unknown alias, missing compiler-version validation, exact predicate over unrelated text, or a bare `--version` token | deny `W-WIN-CC-001` |
| Canonical target `CC` alias through validated `CC`, and a real join/sed transformation of queried output | no finding |
| Diagnostic-only derived text, fabricated array or interpolated-prefix join, exact regex only in a diagnostic, quoted target `GITHUB_ENV` export, wildcard or doubled PowerShell dots, `123.1.x`, `23.1.xbad`, or an added LLVM 18 regex alternative | deny `W-WIN-CC-001` |
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
- The focused native shell contract passes all five executable selection cases.
- Exact-head static review is pending for the scoped four-finding correction.
- Final scoped review of source commit `6434d0fb0e2` is HOLD with P0=0/P1=2:
  a queried symbol in throw text can bind an unrelated metadata predicate, and
  regex concatenation can append an LLVM 18 alternative. The three-cycle cap
  prohibits another source/test correction in this session.
