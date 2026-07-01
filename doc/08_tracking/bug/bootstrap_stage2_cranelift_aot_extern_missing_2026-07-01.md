# Bootstrap Stage2 Missing Cranelift AOT Extern

Status: open
Date: 2026-07-01

## Symptom

`sh scripts/bootstrap/bootstrap-from-scratch.sh --deploy` fails during stage2
native build after the bootstrap worker starts compiling:

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
`simple spipe-mcp ...` shortcut until this bootstrap extern mismatch is fixed.
