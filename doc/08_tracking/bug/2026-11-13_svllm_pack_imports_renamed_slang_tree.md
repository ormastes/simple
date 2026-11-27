# svllm_pack imports a `svllm` module tree that was renamed to `slang`

Status: confirmed genuine product bug (compile error: unresolvable module).
The `svllm-pack` CLI cannot compile on any host.

## Evidence

```
simple run src/app/svllm_pack/main.spl --help
# error: semantic: Cannot resolve module:
#   std.gc_async_mut.svllm.model_executor.model_loader.safetensors
```

exit code 1. `src/app/svllm_pack/main.spl:16-20` imports five modules under
`std.gc_async_mut.svllm...`:

- `svllm.model_executor.model_loader.safetensors`
  (`parse_safetensors_header`, `SafetensorsHeader`, `SafetensorsTensorEntry`)
- `svllm.model_executor.model_loader.tensor_pack`
  (`TensorPack`, `TensorInfo`, `ChunkInfo`, `plan_chunks`, `write_chunk`, `sha256_chunk`)
- `svllm.model_executor.model_loader.manifest` (`serialize_manifest`)
- `svllm.nvfs_client` (`ObjClass`, `CreateFlags`, `OpenMode`)
- `svllm.nvfs_client.std_fs` (`StdFsNvfsClient`, `publish_staged`)

There is **no** `src/lib/gc_async_mut/svllm/` directory. The same modules exist
under `src/lib/gc_async_mut/slang/...` (the model-loader tree, `nvfs_client/`,
etc.), i.e. the library was renamed `svllm` -> `slang`. Even after an import
rename the app would still not compile:

- the `slang` submodules declare their functions/structs **private**
  (`fn parse_safetensors_header`, `struct SafetensorsHeader`, ...), so a direct
  submodule import hits the same visibility wall as the registry modules;
- `slang/nvfs_client/std_fs.spl` contains **no** `StdFsNvfsClient` or
  `publish_staged` symbols under those names.

## Cause and scope

The `svllm_pack` CLI (safetensors -> tensor_pack converter) was authored against
a planned `svllm` module namespace; the underlying engine library shipped as
`slang` with different visibility and different symbol names. This is not a
one-line fix: it needs an import migration plus a `slang` visibility/symbol
audit across `model_loader.safetensors`, `tensor_pack`, `manifest`, and
`nvfs_client.std_fs`, in a core LLM-engine library owned by another lane.

## Correctness gate for a repair

1. Decide the canonical namespace (`svllm` vs `slang`) and rename one side so
   the app's imports resolve; do not leave both trees.
2. Export the consumed `slang` symbols (`pub` or an `__init__.spl` allow-list)
   and reconcile `StdFsNvfsClient` / `publish_staged` with the real
   `nvfs_client.std_fs` API.
3. Re-run `test/02_integration/app/svllm_pack_log_modes_spec.spl`; its four
   red scenarios (help, json usage, dot progress, unknown-option json) must
   pass, and `slang` unit specs must stay green.
