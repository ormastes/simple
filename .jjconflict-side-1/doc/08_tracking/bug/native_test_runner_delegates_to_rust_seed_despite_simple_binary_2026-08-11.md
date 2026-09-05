# Native test runner delegates to Rust seed despite `SIMPLE_BINARY`

## Status

Open; blocks native DrawIR and rendering receipt verification.

## Reproduction

```sh
SIMPLE_BINARY="$PWD/build/native_probe/simple" \
SIMPLE_TIMEOUT_SECONDS=300 \
build/native_probe/simple test \
  test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_damage_replay_spec.spl \
  --mode=native
```

`build/native_probe/simple` is a full pure-Simple CLI and its interpreter test
command works. Native mode nevertheless invokes the deployed Rust bootstrap
seed, prints the seed-only warning, then calls `compile` without its source
argument. The runner exits 1 before compiling any test assertion. Explicit
`SIMPLE_BINARY` does not change the delegated executable.

## Required resolution

The native test compiler owner must resolve and receipt the exact compiler path
once, honor `SIMPLE_BINARY`, reject seed identity, and pass the source argument
to `compile`. Add a sabotage test with a fake seed and assert it is never
executed. Native rendering evidence remains inadmissible until the receipt
records the pure-Simple compiler identity and the focused spec executes.

## 2026-08-11 source repair and remaining deployment gap

`test_executor_parsing.find_simple_binary()` now resolves the canonical
`SIMPLE_BINARY` before argv, legacy `SIMPLE_RUNTIME`, and deployed fallbacks.
The focused ordering contract passes 1/1 in interpreter mode. The deployed
`build/native_probe/simple` still embeds the pre-repair runner. Attempting to
load the current runner from source reaches an existing compiler parse failure
in `src/compiler/80.driver/driver_aot_vhdl_output.spl`, so no refreshed
pure-Simple CLI could be produced in this verification cycle. Native admission
therefore remains open until the repaired runner is rebuilt and the live
sabotage test proves the seed is never executed.
