# Dynamic backend loader acceptance

The canonical behavioral spec is
`test/01_unit/compiler/backend_plugin/dynamic_loader_spec.spl`. It must use
real C shared libraries and the production `load_dynamic_backend_plugin_lease`
boundary. Source-text checks and constructed error enums do not qualify.

The accepted flow proves that the loader:

1. copies a selected provider into a private stage and hashes those copied bytes;
2. remains bound to the staged bytes after the selected source is changed;
3. loads a provider that exports exactly `simple_backend_plugin_v1`;
4. rejects a loadable provider without that symbol and removes its stage; and
5. closes a successful lease, observes the C unload marker, clears its admitted
   handle, and removes its stage.

Run the structural regression first, then the behavioral spec:

```sh
sh test/01_unit/scripts/dynamic_loader_real_execution_contract_test.shs
bin/simple test test/01_unit/compiler/backend_plugin/dynamic_loader_spec.spl
```

On Windows the fixture builder admits only LLVM 23.1.1 `clang-cl.exe` at the
repository-authorized path and SHA-256. It never selects `cl.exe`, GCC, G++,
MinGW, or `clang++`. Other hosts compile the same C fixtures with `clang`.

The TODO remains open until this spec passes on a source-matched self-hosted
binary. A bootstrap-seed run is diagnostic evidence only.
