# MSVC default libraries omit the hosted WinHTTP dependency

- ID: `windows_msvc_default_libraries_missing_winhttp_2026-11-07`
- Severity: P1
- Owner: `src/compiler/70.backend/linker/msvc.spl`
- Status: source repaired; native linker regression passed; source-matched Simple compiler replay pending.

The attempt-11 Stage 2 frontend admission in the isolated node-attribute
bootstrap checkout recorded two distinct failures. The bounded `p2_add` build
timed out after 180 seconds and its Windows Job was reaped. Separately, the
preceding SCV prime reached native code generation and failed at MSVC linking.
Its retained full worker log, `native-build-stderr-25976-2.log`, records native
compilation complete at 4,686 ms and link start at 4,688 ms. Eleven `WinHttp*`
imports were unresolved. The emitted library list omitted `winhttp.lib`.

The rejected candidate SHA-256 was
`3d715b003758cb3df4f09883c3fce9ee2baeec3d3b12c6fdec1043849346a2a0`.
The timeout is not evidence of a MIR failure or a deadlock. Neither failed
admission nor the SCV prime is a successful compiler qualification.

`default_windows_libs_with_suffix()` supplies `MsvcConfig.default()`, including
the executable link path exercised here. Other shared/native-all library lists
already contained WinHTTP, but they did not repair this default. Release
`ac574f19fa4ebc8e40f14a1b24b498051e4423a5` still had the omission. The fix adds
`winhttp.lib` to the existing default list without changing other libraries.

## Executed native regression

`scripts/check/check-msvc-default-winhttp-windows.ps1` reads the actual Simple
default library list, compiles a tiny import consumer, and invokes the real
Windows linker. It performs no HTTP request: the executable creates and closes
a local WinHTTP session. Each compile/link is bounded at 30 seconds and execution
at five seconds. Private output directories retain logs, objects and the result.

Using LLVM 23.1.1 `clang-cl.exe`/`lld-link.exe`, Windows SDK 10.0.26100.0 and
MSVC 14.44.35207 x64 libraries:

- Before the repair, linking with the actual default list failed with unresolved
  `WinHttpOpen` and `WinHttpCloseHandle`.
- After the repair, a negative control removing only `winhttp.lib` still failed
  with the expected WinHTTP import diagnostic.
- Linking with the repaired default list succeeded, and the resulting native
  executable returned zero after opening and closing its session.

Evidence is under the feature worktree's
`build/node-attributes-qualification/winhttp-default-before-20261107` and
`winhttp-default-after-20261107`. The latter includes `result.sdn` binding the
tested source owner hash. This verifies the native link recipe, not execution
of the Simple `MsvcConfig` implementation or full compiler admission.

One real API case was added to `msvc_linker_candidate_spec.spl`, checking both
the default configuration and generated linker arguments. That Simple case
remains unexecuted until an admitted self-hosted runner is available. The new
bug has a concrete report; ledger registration/validation was not claimed.
