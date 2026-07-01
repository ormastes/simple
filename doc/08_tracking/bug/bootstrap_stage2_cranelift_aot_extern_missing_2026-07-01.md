# Bootstrap Stage2 Missing Cranelift AOT Extern

Status: partially fixed
Date: 2026-07-01

## Symptom

`sh scripts/bootstrap/bootstrap-from-scratch.sh --deploy` failed during stage2
native build after the bootstrap worker started compiling:

```text
error: semantic: unknown extern function: rt_cranelift_new_aot_module
error: native-build worker exited with code 1 (no binary produced).
```

## Repro

```sh
scripts/resource/run_capped.shs sh scripts/bootstrap/bootstrap-from-scratch.sh --deploy
```

The stage log is:

```text
build/bootstrap/logs/x86_64-unknown-linux-gnu/stage2-native-build.log
```

## Impact

The SPipe MCP source-mode CLI works, but the deployed self-hosted
`bin/release/simple` wrapper cannot be refreshed to expose the new
`simple spipe-mcp ...` shortcut until bootstrap deploy completes.

## 2026-07-01 Update

Fixed the missing ELF runtime resolver entries for:

- `rt_cranelift_new_aot_module`
- `rt_cranelift_aot_define_function`

Focused proof:

```sh
cargo test -p simple-compiler elf_utils::tests::resolves_cranelift_aot_runtime_symbols
```

Stage2 then advances when the worker uses the rebuilt bootstrap seed. Deploy is
still blocked later: Stage4 writes a tiny full CLI binary
`build/bootstrap/full/x86_64-unknown-linux-gnu/simple` that exits with no output,
so the bootstrap script refuses to deploy it:

```text
error: stage4 binary failed smoke test (-c 'print(1+1)' -> '')
```

## 2026-07-01 Stage4 Update

The Stage4 tiny-binary cause was the deploy script exporting
`SIMPLE_BOOTSTRAP=1` globally and then reusing that environment for full app
native builds. Stage4 and Stage5 now run their native-build commands with
`SIMPLE_BOOTSTRAP` unset so `src/app/cli/main.spl` and MCP entries do not route
through the bootstrap-main-only driver path.

Focused proof:

```sh
sh -n scripts/bootstrap/bootstrap-from-scratch.sh
bin/release/simple check src/app/spipe_mcp/main.spl src/lib/nogc_sync_mut/spipe/tree_context.spl
```

Full deploy was not re-proven in the isolated
`simple-spipe-mcp-parser-cli-20260701` workspace: Stage2 consumed CPU for
several minutes with no new stage output and was stopped to avoid a runaway.
The next deploy attempt should start from a fresh workspace or update the
native-build worker monitor/launcher path first.

## 2026-07-01 Worker Launcher Update

`native_build_main.spl` already honors `SIMPLE_BINARY` before falling back to
`bin/simple`. The bootstrap script now sets `SIMPLE_BINARY` to the active stage
compiler for Stage2, Stage3, Stage4, and Stage5 native-build worker launches.
This removes the need for a temporary `bin/simple` wrapper in linked workspaces
and avoids the host monitor rule that kills long `bin/simple run
...native_build_worker...` commands.

Focused proof:

```sh
sh -n scripts/bootstrap/bootstrap-from-scratch.sh
timeout 35 sh scripts/bootstrap/bootstrap-from-scratch.sh --pure-simple --native-timeout=1 --no-mcp
```

The bounded probe reaches Stage2 and the worker exits through the expected
one-second timeout path instead of failing with `bin/simple: No such file or
directory`.

## 2026-07-01 Bounded Deploy Probe

After the launcher fix, a bounded deploy probe:

```sh
timeout 300 sh scripts/bootstrap/bootstrap-from-scratch.sh --pure-simple --native-timeout=3600 --no-mcp
```

still remained in Stage2 until the outer 300-second cap exited with code 124.
The Stage2 log showed the correct worker launcher:

```text
SIMPLE_BINARY=src/compiler_rust/target/bootstrap/simple src/compiler_rust/target/bootstrap/simple native-build ...
```

No fresh Stage2 binary was produced within the cap. The current deploy blocker
is Stage2 bootstrap build duration/progress, not missing worker launcher,
missing Cranelift AOT resolver symbols, or the Stage4 bootstrap-mode leak.

## 2026-07-01 Stage2 Rust-Handler Route

`native-build` is classified as a pure-Simple tool, so its normal command-table
env override path is skipped. The Rust seed already has an in-process
`handle_native_build` implementation, and the bootstrap Stage2 build is exactly
the place where the interpreted pure-Simple worker is too slow. The driver now
honors `SIMPLE_NATIVE_BUILD_RUST=1` for `native-build`, and Stage2 sets that
env var when invoking the Rust seed. Normal host `simple native-build` behavior
is unchanged.

Focused proof after rebuilding `src/compiler_rust/target/bootstrap/simple`:

```sh
timeout 180 env RUST_LOG=error SIMPLE_BINARY=src/compiler_rust/target/bootstrap/simple \
  SIMPLE_NATIVE_BUILD_RUST=1 src/compiler_rust/target/bootstrap/simple native-build \
  --timeout 300 --backend cranelift --source src/compiler --source src/app \
  --source src/lib --entry-closure --entry src/app/cli/bootstrap_main.spl \
  --runtime-path "$PWD/src/compiler_rust/target/bootstrap" \
  -o /tmp/spipe_stage2_direct.bin
```

Result: linked a 6.6 MB Stage2 bootstrap compiler in 1.7 seconds and
`/tmp/spipe_stage2_direct.bin --help` printed the bootstrap compiler help.

The same Rust-handler route is now used for seed-backed Stage4 and Stage5.
Direct Stage4 proof:

```sh
timeout 240 env -u SIMPLE_BOOTSTRAP RUST_LOG=error \
  SIMPLE_BINARY=src/compiler_rust/target/bootstrap/simple \
  SIMPLE_NATIVE_BUILD_RUST=1 LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING=1 \
  src/compiler_rust/target/bootstrap/simple native-build \
  --timeout 300 --backend cranelift --source src/compiler --source src/app \
  --source src/lib --entry-closure --entry src/app/cli/main.spl \
  --runtime-path "$PWD/src/compiler_rust/target/bootstrap" \
  -o /tmp/spipe_stage4_direct.bin
```

Initial result: linked a 42 MB full CLI in 166.7 seconds. `--help` printed the
full CLI help and included `simple spipe-mcp [serve|parsers|...]`, but both
`-c 'print(1+1)'` and `spipe-mcp parsers` exited 248 with no output because
those paths used nested file/code runner hooks.

The `spipe-mcp` CLI wrapper now calls `app.spipe_mcp.main.spipe_mcp_run(args)`
directly instead of routing through `cli_run_file("src/app/spipe_mcp/main.spl",
...)`. Rebuilding the Stage4 binary then proves:

```sh
/tmp/spipe_stage4_direct.bin spipe-mcp parsers
```

returns parser names with exit 0. The current deploy blocker is now the broader
Stage4 generated-binary `-c 'print(1+1)'` smoke, which still exits 248 with no
output; the bootstrap script correctly refuses to deploy a general `bin/simple`
that cannot run code snippets.

Older revisions may need a temporary `bin/simple` wrapper to the rebuilt
bootstrap seed while running the staged worker; current bootstrap runs pass the
active stage compiler through `SIMPLE_BINARY` instead.
