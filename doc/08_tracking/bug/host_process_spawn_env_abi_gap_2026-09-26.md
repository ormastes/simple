# Hosted process spawn with explicit environment has no matching runtime ABI

**Status:** Open — source route mismatch; runtime reproduction and repair pending.
**Affected route:** `app.io.process_spawn_async_env` and any hosted SOSIX
`ProcessLaunchSpecV1` provider that would rely on it.

## Source evidence

- `src/app/io/process_env_ops.spl` declares
  `rt_process_spawn_async(cmd: text, args: [text], env: {text: text})` and passes
  an environment map as its third source argument.
- `src/compiler_rust/compiler/src/interpreter_extern/system.rs` implements
  `rt_process_spawn_async` through `process_spawn(args, false)`. That function
  requires at least two arguments, reads `args[0]` and `args[1]`, and never
  reads `args[2]`. It creates `std::process::Command` without applying the
  requested environment map.
- `src/lib/nogc_sync_mut/io/process_ops.spl` owns a separate two-argument
  declaration and uses it for the normal hosted spawn path.
- `src/runtime/runtime_legacy_core.c` defines the native symbol as
  `rt_process_spawn_async(const char* cmd, const char** args, int64_t arg_count)`.
  There is no map-taking native symbol at this route. The source-level
  three-argument declaration is not evidence of a compatible C ABI.
- The same two-argument route also has an observable stdio split: the Rust
  interpreter configures child stdin as null and stdout/stderr as inherited,
  while the C `fork`/`execvp` path inherits all three descriptors. The shared
  launch contract cannot safely infer one stdio policy from this symbol.

The interpreter's environment loss follows directly from its dispatch code.
The native behavior needs a compiled ABI test; do not infer that the map is
applied, or claim a specific native failure mode, from the declarations alone.

## Required correction

The hosted process-service owner needs one versioned spawn operation that
accepts the complete validated `ProcessLaunchSpecV1`: executable, argv,
environment, cwd, stdio bindings, resource limits, namespace, runtime profile,
capabilities, service grants, and affinity. Each provider must implement a
field or refuse it before spawning; no field may be silently ignored. The
interpreter and native backends must share the same observable contract.

The existing two-argument spawn may remain a compatibility operation. The
three-argument app wrapper must use a provider with proven map semantics or
return an explicit unsupported result; it must not be used as the SOSIX launch
provider on current source evidence.

## Acceptance evidence

Use a child executable that reports its environment and working directory to
an isolated output channel. For interpreter, native, and SimpleOS profiles,
prove that an explicit variable reaches the child, an absent variable remains
absent according to the selected inheritance policy, argv boundaries are
preserved, and unsupported stdio/resource/grant fields refuse before child
creation. Verify exit notification and cleanup through the same service owner.

No source-matched pure-Simple runner is available in this worktree, and this
report is not a runtime PASS.
