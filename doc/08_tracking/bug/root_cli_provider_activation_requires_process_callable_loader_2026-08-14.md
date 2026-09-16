# Root CLI provider activation requires a process-callable loader

## Status

Open. The separately targetable in-process proof lives at
`src/app/provider_cli/main.spl`; it is not wired into the root command table.
`src/os/smf/provider_loader.spl` now performs path, SHA-256 artifact identity,
capability, host/interface version, loader, symbol, and process-callability
admission. `provider_generation.spl` owns atomic in-process replacement and pin
lifetime. The exact query-call and owned-session slices now exist, but the root
CLI still does not bind them to an SCI command record.

## Evidence

- `src/app/cli/dispatch.spl:47-96` resolves static `CommandEntry.app_path` and
  invokes source through `cli_run_file`; it has no provider-artifact admission,
  query-entry, descriptor-prefix, generation-pin, or capability-grant path.
- `src/app/cli/_CliMain/main_and_help.spl:591-605` treats an existing source
  path as the final generic execution fallback. Adding a provider token here
  would broaden the root's static dispatch surface without supplying a loader.
- `src/app/startup/dynsmf_autoload.spl:21-55` owns a background shell compile
  path and session evidence, not a proved process-callable
  `simple_provider_query_v1` address. Lines 59-67 correctly avoid spawning it
  during startup.

## Impact

The `SimpleProviderQueryV1` and `SimpleCliCommandV1` semantics are executable
in-process and the provider CLI is separately targetable, but `.so`, `.dylib`,
`.dll`, and `.smf` leaf commands cannot honestly be routed from the root CLI.
Pretending otherwise would turn registry evidence into an unsafe function call
or reintroduce startup compilation.

## Unblock condition

The loader/client integration must invoke the verified query address through a
versioned raw-buffer bridge, validate the returned descriptor prefix and stable
interface set, add signature/target evidence not yet present in admission, and
couple the admitted library handle to the generation pin lifetime. Both loader
families must use the same provider contract and fail closed when any proof is
absent. After focused native/SMF old/new version and unload-pin tests pass, the
root CLI may add one generic SCI command-registry hook instead of per-provider
imports.

## 2026-08-14 progress

The hosted and native runtimes now expose the exact `int32`
`rt_provider_query_v1_call` ABI; Simple marshals canonical 44-byte request and
60-byte result buffers without exposing language-private layouts. Dynamic
admission retains its `DynLibKind`, successful query results receive unique
session pins, release rejects replay, and close refuses live pins.

Still required: run a real native/SMF provider through an admitted B2/B3 tool,
validate signature/target evidence, then connect the generic SCI route to the
root executable. Source and Rust-runtime checks do not prove deployed dispatch.

## Prohibited workaround

Do not call `dynsmf_dispatch_background_compiles` from startup or command
dispatch, construct shell commands for missing providers, import provider
implementations into the root CLI, or fall back to the Rust seed.
