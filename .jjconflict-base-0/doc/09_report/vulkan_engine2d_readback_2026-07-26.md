# Vulkan Engine2D Readback Evidence

- status: blocked
- reason: cross-module `Engine2DReadback.pixels` field index mismatch
- host: Linux x86_64
- ICD: `/usr/share/vulkan/icd.d/nvidia_icd.json`
- execution mode: native, no stub fallback

## Source-Matched Compiler

`build/gpu-goal/source-matched/simple` was built incrementally from the fixed
compiler source:

```text
Build complete: 3 compiled, 682 cached, 0 failed
Time: 20.0s compile + 59.7s link
```

No Stage2, Stage4, Cargo build, bootstrap script, cache deletion, or seed
fallback ran.

## Evidence Build

The source-matched compiler emitted the 184-module Engine2D evidence closure.
The guarded core link correctly rejected unrelated optional GPU symbols. A
direct no-stub link of the retained objects then succeeded with the existing
optional-GPU provider archive and current quarantine-lock provider.

## Latest Execution

Retaining the provider-only archive member reaches live hardware:

```text
vulkan_probe_available=true
status=Initialized
compute=true
graphics=true
strict_create_status=pass
backend_name=vulkan
```

The next instruction path segfaults. Static disassembly shows the producer
allocating a 48-byte `Engine2DReadback` with `pixels` at offset 0, while the
caller loads `pixels` from offset `0x50`. The aggregate pointer is already
untagged, so this is a field-layout metadata mismatch caused by per-module
numeric `SymbolId` collision.

The MIR source now prefers name-keyed lowered-value provenance before numeric
HIR IDs and preserves owner-qualified aggregate returns across every method
dispatch path. Its final layout source contract passes 2/2. The follow-up
Dict-dispatch source contract passes 3/3: nonstatic Dict builtins now validate
the lowered receiver even when stale resolution names an unrelated `.has`, and
the first-stage HIR membership checks use the direct runtime owner.

The first three bounded retained-cache builds completed at 6 compiled/729
cached, 3/732, and 4/731. A second bounded session completed at 5/730, 4/731,
and 5/730. Canonical text mode transport now survives every aggregate copy and
the driver enters AOT instead of falsely succeeding without output. The next
crash is in `optimizationpipeline_for_backend`, called by
`optimize_module_for_backend` and `CompilerDriver.optimize_mir`; no oracle
binary was emitted. The executable same-name and CLI-mode regressions are
present but remain unexecuted behind that optimizer aggregate-path defect.

macOS Metal live evidence is explicitly postponed to a prepared host by
`gpu_backend_mac_host_remaining.md`; its host-gated system spec requires real
source markers and native receipt fields and does not claim Linux evidence. No
additional hardware run was made, and readback/checksum/parity pass is not
claimed.

See
`doc/08_tracking/bug/native_engine2d_readback_cross_module_field_layout_2026-07-26.md`.

## Link-Owner Repair

The canonical native link owner now scans only explicitly selected static
provider archives, roots the strong `rt_vulkan_provider_is_available` member,
and supplies the platform's executable dynamic-export visibility for the core
runtime's lookup. ELF and MSVC export the named symbol; Darwin uses
executable-wide dynamic export. MinGW retains the member but does not receive
the ELF-only export flag because its provider lookup owner is separate. The
root still retains only one named member rather than force-loading the complete
optional-GPU archive.

The host-independent weak-first archive fixture mirrors that runtime lookup
without a direct unresolved provider reference. It records baseline
availability `0` and retained-provider availability `73`, proving extraction
and dynamic discoverability. This repair was produced on macOS without a
Linux/Vulkan live cycle. The blocked Linux execution above remains the current
device evidence; no availability, handle, readback, checksum, or parity PASS is
added by the owner fixture.

The next Linux session isolated the compiler blocker further. Native
`OptimizationConfig.Enabled(2)` lost its payload and entered the backend
optimizer as `NoOpt`; the driver now uses scalar level transport and direct
`OptLevel` literals. Three bounded commands using the retained cache then
failed at the admitted `core-c-bootstrap` link. Missing providers include
`str.to_lowercase`, `rt_string_free`, and `rt_cranelift_*`; the historical
runtime-path attempt added unresolved `spl_*` dependencies. No stub fallback,
full bootstrap, `84` oracle, or Vulkan run was accepted.

## Optimized Runtime Revalidation

Later current-source evidence supersedes the blocked Linux status above for the
ProcessingIR Vulkan probe. Commit `b658e408064a` replaces exported per-element
RuntimeArray conversion calls with checked direct slice loops. CUDA/Vulkan
runtime archive
`3d24c72e59735791941983517cc222ff5fc9a4112b668ef098dbfa4ceab244c0`
links strict no-stub probe
`fd9fa68a06ac4eb32182eab5bcc19095aaed89ceb8220078c89e229e045bdd4d`.

The canonical hardware gate passes:

- exact 64-value Vulkan result with handle/identity `666008366`;
- unavailable, init, submit, readback, and mismatch failures with exact reasons,
  empty output, and zero provenance;
- same-process submit failure followed by exact recovery with unchanged
  identity.

The retained gate log is
`build/simpleos_gpu_host/vulkan_fault_native/optimized-runtime-gate.log`.
This closes Linux revalidation of the shared conversion optimization. It does
not claim prepared-host Metal or macOS Vulkan execution.

## Canonical Probe Refresh

On 2026-07-28 the canonical probe paths still named older binaries. The CUDA
binary returned a checksum eight times the expected value even though the
newer recovery-capable artifact passed exact device readback. The verified
artifacts were promoted byte-for-byte to the canonical paths:

- CUDA: `10323c8438ed987a2610793aa6af680933ae20e933ce0f3c11fcdbc281259519`
- Vulkan: `106e0c5e35acf33810dde296099fa3010ed4f1d0a16f6e064efe9259a25c2a19`

The combined gate then passed exact CUDA output with no CPU fallback, exact
Vulkan output, all five typed failure phases, and same-process recovery. The
receipt is `build/gpu-goal/evidence/processing-cuda-vulkan-native-parity-2026-07-28.log`.
The durable receipt values are CUDA count 64, checksum 1082179840, handle 1,
identity 1002905313239842438, `cpu_fallback=false`; and Vulkan count 64,
handle/identity 666008366, all five injected failures classified correctly,
followed by exact recovery with stable identity.
