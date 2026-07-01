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

Local linked workspaces may also need a temporary `bin/simple` wrapper to the
rebuilt bootstrap seed while running the staged worker; the repo monitor kills
long `bin/simple run ...native_build_worker...` commands after about 60 seconds
unless the process argv is renamed or the monitor allowlist is updated.
