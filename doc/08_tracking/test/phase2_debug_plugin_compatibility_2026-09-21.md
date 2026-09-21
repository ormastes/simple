# Phase 2 debug and GPU mapper compatibility evidence

## Reproduction

The retained Stage 2 test-runner build failed in
`src/lib/nogc_async_mut/debug/coordinator.spl` on optional trait receiver
dispatch and in both GPU type mappers on aggregate reductions.

The new behavioral fixtures reproduce those paths:

- `coordinator_info_provider_dispatch_spec.spl` exercises both address mapping
  directions through the registered optional provider.
- `gpu_type_mapper_aggregate_alignment_spec.spl` exercises mixed-width tuple
  alignment in the CUDA and Vulkan mappers.

Against the unmodified PR sources, focused native compilation failed with
unresolved `DebugBackend.attach`, `Array.enumerate`, and `Array.max` calls.
With this change, both fixture binaries compiled and executed: three examples,
zero failures. The three affected production entries also completed LLVM
codegen with zero failed files.

## Performance and memory assessment

A cold-cache focused build of the GPU fixture completed in 33.33 seconds with
289,898,496 bytes peak RSS on macOS arm64. The explicit single-pass reductions
avoid temporary mapped arrays and remain linear in aggregate member count.
The debug change adds one constant-size bridge object at registration and no
work in request loops beyond one direct forwarding call. The focused debug
fixture compiled in 263.1 seconds before execution; its broad 299-module
closure dominates that time.

## SoSIX compatibility audit

The diff adds no extern declarations, runtime symbols, host ABI types, process
calls, environment reads, device calls, or facade exports. Public registration
and query signatures remain unchanged. The debug bridge only preserves the
existing trait dispatch behind a concrete private owner. GPU mapper output and
empty-aggregate alignment remain unchanged; only local collection reductions
were replaced with explicit loops. Therefore host ABI, runtime, facade,
process, and device contracts are unchanged.
