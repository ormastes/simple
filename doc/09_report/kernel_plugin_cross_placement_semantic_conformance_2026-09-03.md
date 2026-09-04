# KPF Cross-Placement Semantic Conformance

**Status:** Implemented and focused-pass verified  
**Date:** 2026-09-03

## Scope

The canonical `SimpleCliCommandV1` run operation now has one executable semantic
oracle across static-direct, sealed static-table, admitted native, supervised
real-worker, and the currently supported deterministic Wasm-component adapter.
The native lane uses the production SMF/native loader, cached admitted session,
provider query, CLI invoke entry, generation pin, release, and unload path.

The probe seals and round-trips a real `SimpleCompositionImageV1`, publishes and
pins the matching immutable KPF generation, runs the same `native-provider-ok`
payload through every placement, then releases the generation pin. A mismatch
has a placement-specific nonzero exit status.

## Evidence

- Probe: `src/app/test/kpf_cross_placement_conformance.spl`
- System runner: `test/03_system/compiler/feature/kernel_plugin/cross_placement_semantic_conformance_test.shs`
- Mutation guard: `test/01_unit/scripts/kpf_cross_placement_semantic_mutation_test.shs`
- Native admitted-session operation: `src/os/smf/kernel_plugin/native_loader.spl`

## Architecture

No new loader, registry, or transport was introduced. Static-table uses
`KpfStaticRegistry`; native uses `KpfSmfNativeSessionV1`; worker uses
`KpfRealWorkerTransportV1`; Wasm uses `KpfWasmComponentTransportV1`. The Wasm
host remains the repository's deterministic supported component host, so this
is adapter-semantic parity rather than external Wasmtime qualification.

## Results

- Cross-placement system scenarios: **2/2 PASS**.
- Placement result checks use distinct failure codes, and the structural
  mutation guard proves each adapter remains connected to the shared oracle.
- Authenticated SCI byte mutation: **rejected** before dispatch.
