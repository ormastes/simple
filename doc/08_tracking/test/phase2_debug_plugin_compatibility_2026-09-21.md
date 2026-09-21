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

Final-source cold-cache profiles used the admitted Stage 2 compiler, disabled
HIR/frontend caches, and isolated native cache scopes on macOS arm64:

| Fixture | Modules | Wall time | Max RSS | Result |
|---|---:|---:|---:|---|
| GPU mapper | 72 | 21.27 s | 383,451,136 bytes | 2 examples, 0 failures |
| Debug provider | 299 | 269.44 s | 704,757,760 bytes | 1 example, 0 failures |

Both focused compiles remain below the 1 GiB compile target. The indexed
collection builders and explicit alignment reductions remain linear in
aggregate member count. The debug change adds one constant-size bridge object
at registration and no work in request loops beyond one direct forwarding
call. The broad debug closure dominates its compile time.

## Final-source receipt

The profiles above were rebuilt after the final Astra performance review at
source commit `de63f6d813d`. `SIMPLE_ALLOW_UNRESOLVED_RUNTIME=1` admitted only
the repository's pre-existing optional/runtime-link gaps; both produced
binaries executed successfully, so none of those stubs were reached.

| Item | SHA-256 |
|---|---|
| Stage 2 compiler snapshot | `35acf59774028cb8849812abf5762330dfd16f232dacb9bb3b278f176e8b0669` |
| CUDA mapper source | `51a16b3c44d185f94b2e84c6694c41ca14c5bbba4deca00f54a0ab44f0bacc65` |
| Vulkan mapper source | `a1606aa701ede59693014e243df9797ae97a957b40eea562ebf6f7f1f27dcb0a` |
| Debug coordinator source | `a7eceb820003a55aaac0e37c965703449f40b2bb487ce86c8685819017f308ac` |
| GPU fixture source | `17cbecd83aef1e5e47f893b76a73468552c7492d435047ba648e11ea4944a7d5` |
| Debug fixture source | `41d5cc9dd6fb7725125ae4119031becc31741a878e000a2d008405bf1d2dd55f` |
| GPU fixture binary | `8607fb7f7e58bdb85e4b3334a051bc622d4873eb8d4d2147ed5b9b24cde5cdc8` |
| Debug fixture binary | `59fac0bed1c1b11a39adae570258a45c33eb949fc8c9a46bc2505288d9a1aba0` |

## SoSIX compatibility audit

The diff adds no extern declarations, runtime symbols, host ABI types, process
calls, environment reads, device calls, or facade exports. Public registration
and query signatures remain unchanged. The debug bridge only preserves the
existing trait dispatch behind a concrete private owner. GPU mapper output and
empty-aggregate alignment remain unchanged; only local collection reductions
were replaced with explicit loops. Therefore host ABI, runtime, facade,
process, and device contracts are unchanged.
