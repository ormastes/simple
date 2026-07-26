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
HIR IDs. Its isolated regression passes 1/1. Three bounded incremental compiler
build attempts did not produce a usable source-matched CLI; the final attempt
stopped on 14 unrelated cached LLVM undeclared-global failures. No additional
hardware run was made, and readback/checksum/parity pass is not claimed.

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
