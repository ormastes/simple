# Core MSVC native links omit WinHTTP

ID: `windows_msvc_core_native_link_missing_winhttp_2026_11_06`.
Severity: P2. Status: OPEN; source-confirmed, current-source native verification pending.
Target: `release/1.0.0`; inspected base `6faea9af40b79ed718f831906d29e09b07da12bd`.

The Windows core runtime calls WinHttpCrackUrl, WinHttpOpen and related APIs
in `src/runtime/runtime_native.c`. The ordinary native executable MSVC link
paths in `_LinkerWrapper/native_linking.spl` omit `winhttp.lib` from both
`link_native_windows_with_engine`'s internal COFF support list and
`_link_native_msvc_with_engine`'s external linker list. Their shared-library
and native-all counterparts already include this import library. The
native-all support helper returns an empty list for ordinary core-only inputs,
so that separate table does not establish core executable coverage.

Earlier frozen-producer MSVC Hello diagnostics in the repair campaign contain
unresolved WinHTTP imports after SDK library discovery was corrected. Those
logs are supporting symptom evidence, not proof that a compiler rebuilt from
the inspected source has executed the regression.

Required repair: include the existing Windows SDK `winhttp.lib` in both native
MSVC support lists without changing other targets or library precedence.
Required evidence: a current-source self-hosted producer compiles and links
the real native Hello with the core runtime and executes its output; cover
both internal COFF and external MSVC link paths, keeping unsupported internal
features visible rather than treating a refusal as a pass. Inspect generated
link inputs for WinHTTP. Core/compiler/MCP verification remains required.

The prerequisite bootstrap source remains isolated from the unqualified cache
draft and the deferred MIR call-origin ABI design. No tag or deployment is
authorized by this report, and no native assertion PASS is claimed.

Draft source repair: `winhttp.lib` is now added immediately after `ws2_32.lib`
in both existing lists. Library order, native-all merging and the internal
linker's optional discovery behavior remain intact. Independent source review
confirmed this is the minimal repair; actual native import closure remains
unproven. This draft must not be marked fixed or landed before qualification.

The executable fixture `test/fixtures/compiler/windows_msvc_winhttp_link.spl`
forces real WinHTTP imports even when an archive linker discards unused core
HTTP code. It opens a no-proxy session, closes it and requires the exact success
line `WinHTTP link OK` with exit0. It sends no request. Execute it using both
native link engines; an unsupported engine/refused input remains a failure or
unqualified case, never a placeholder pass. No fixture execution yet.
