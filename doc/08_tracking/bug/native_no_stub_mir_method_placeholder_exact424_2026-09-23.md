# Native diagnostic lowers unresolved methods to const zero with no-stub enabled

Status: OPEN; observed on 2026-09-23. No compiler change or accepted probe result.

## Reproduction and lineage

Source `42402d3468e13cfbaf48699c3071f70c647723db` in `D:/b424fresh`; admitted Stage2 compiler SHA-256 `510d70d22d0e909e04bb0f6e37087cea8c1fa1e0af6c8e89340db08b7168f7eb`.

Exact launcher: `D:/b424fresh/build/native_probe/stage3-diagnostic424/probe.sh`.
Entry: `handoff_probe.spl` in that directory. The reduced entry constructs an empty environment-policy collection and exercises canonical handoff encode, strict base64 decode, and policy decode.

The launcher uses the supported direct positional driver route solely for diagnosis, `--threads 12`, LLVM/MSVC, `--mode dynload`, `core-c-bootstrap`, private `probe-cache`, `SIMPLE_NO_STUB_FALLBACK=1`, and a 600-second cap. It does not bypass or mint canonical Stage3 admission. The source/runtime authority remains unchanged.

## Observed evidence

`probe-build.log` contains:

```text
[mir-lower] WARNING: unresolved method call 'bytes' lowered to const-0 placeholder (silent-null risk, Task #145)
[mir-lower] WARNING: unresolved method call 'new' lowered to const-0 placeholder (silent-null risk, Task #145)
[mir-lower] WARNING: unresolved method call 'unwrap' lowered to const-0 placeholder (silent-null risk, Task #145)
```

The responsible fallback is `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:3694`. This report proves execution of the const-zero lowering path while no-stub is enabled; it does not claim that the final linker accepted a stub executable. The reduced probe reached its 600-second limit (`build_exit=124`); no probe executable was produced and no probe result is accepted as correctness evidence.

The earlier app-owner probe log is retained separately as `probe-owner-build.log`; it failed HIR lowering on unresolved I/O facade functions, including `cwd_process`, `env_get_opt`, and `read_file_text`. That failure is distinct from the reduced probe's MIR placeholders.

## Required resolution

Determine why valid method targets in this closure were unresolved. Ensure strict candidate builds cannot silently substitute const zero for unresolved behavior, with a focused negative regression proving rejection and a positive regression proving the real method behavior. Preserve the lean dynload bootstrap architecture. Do not normalize these placeholders as acceptable diagnostic semantics or claim a Stage3/4 pass from this probe.
