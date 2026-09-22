# Phase2 CLI import providers and optional index lowering

Status: focused native probes pass; full CLI / SSpec suite pending integration.
Base: 25d609723cd. Provider/mapper, WASM import, version parsing and ABI spec
ported from PR1259 head 77fb2dd0fd38e5ac99b2c57b03647d87128e995b.
TRACE32 CLI alias follows historical 3224fd51963; its transitive MCP and CMM
aliases resolve existing tracked examples/10_tooling/trace32_tools providers.
No owner limits, runtime code, platform intrinsics or process policy changed.

## Reproduction and fix

Fresh run-3 compiler_cli_build.log reports E1034 for app.t32_cli.mod,
compiler.backend.common.c_abi_type_mapping and plugins.backend_wasm.wasm_codegen_adapter.
The C ABI provider was absent; WASM lives in compiler.backend.wasm_codegen_adapter.
TRACE32 requires three source aliases: t32_cli, mcp_t32 and cmm_lsp.
Restoring only t32_cli exposes missing mcp_t32, then missing cmm_lsp. All three
are now covered by resolver assertions and a compiled executable CLI help closure.
C++ aggregate spellings remain separate from C export ABI fail-closed handling.

The same run reports optional Add in version_manifest._version_value despite
`if val idx = line.index_of(":")` binding. This is a concrete Phase2 optional
pattern-lowering defect; explicit `?? -1` unwrapping avoids it until the compiler
is repaired. PR1259 also moves numeric coalescing out of boolean expressions;
those changes preserve validation behavior and remain compiler compatibility
workarounds, not a claim that compact syntax is invalid. Native assert calls in
the initial standalone probe linked an unresolved `_assert`; fixtures therefore
use distinct nonzero failure exit codes. That unrelated compiler defect remains.

## Evidence

Compiler: /Users/ormastes/simple-tmp/phase2-test-20260922/run-3/compiler.snapshot
SHA256: 531b1b9b270a66e5ed30c0c9311f013ad451d0f17377ddb24f01fce4df372e20
Stage2 only, host-gpu runtime capsule of the same hash; fallback disabled.
Worktree evidence: build/phase2-probe/*.log.

- C ABI provider removed: native fixture fails E1034; 7.63s, 291635200 bytes RSS.
- C ABI provider restored, delimiter present/absent checks: native build succeeds;
  5.56s, 238714880 bytes RSS (65 cached units); executable succeeds, 0.59s,
  8830976 bytes RSS. Cache asymmetry means no speedup claim is justified.
- TRACE32 before transitive aliases: 7.08s, 359612416 bytes RSS; missing mcp_t32.
- TRACE32 with all aliases: 93 compiled / 0 failed, 19.61s, 283279360 bytes RSS;
  executable prints usage and exits 0, 0.41s, 9273344 bytes RSS.
- Added ABI mapping SSpec, resolver assertions, version numeric validation cases,
  and executable fixtures. General SSpec runner remains blocked by the broader
  Phase2 test runner build; these SSpecs are not claimed executed.

Commands use native-build --source src/compiler --source src/app --source src/lib
--entry-closure --entry test/fixtures/compiler/phase2_cli_import_provider_probe.spl
(or phase2_t32_import_provider_probe.spl), --threads 1, isolated cache and outputs.
Process group bounds: C ABI 180s/150s internal, TRACE32 120s/90s internal.

SoSIX review: aliases stay inside the repository and preserve existing modules;
fixes introduce no host calls or OS assumptions. Execution evidence is macOS
arm64 only; no SoSIX runtime compatibility certification is claimed.
