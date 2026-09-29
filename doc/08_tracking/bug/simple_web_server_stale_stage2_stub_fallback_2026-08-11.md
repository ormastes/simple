# Simple web server stale-stage2 unresolved-stub fallback

Status: fixed at the production build gate; a fresh live artifact is still required.

## Exact failure

`build/evidence/simple_web_server_live_smoke/build-cranelift.log` reported a
successful 437-module Cranelift build while manufacturing weak bodies for six
unresolved symbols:

- `__cpu_indicator_init`, `__cpu_model`
- `chr`, `text_dot_from_char_code`
- `lib__nogc_async_mut__io__SyncTcpListener`, `lib__nogc_async_mut__io__SyncTcpStream`

The linked program passed `--check` but exited before opening its listener.
Therefore a successful link containing these generated bodies is not executable
server evidence.

## Ownership

- `__cpu_indicator_init` and `__cpu_model` are compiler-support references from
  `runtime_simd_dispatch.o`. The host `cc`/`clang` driver resolves them from its
  compiler-support library. The native-build pre-link scanner must not fabricate
  application bodies for them before the real linker runs.
- Current pure-Simple MIR lowers integer `.chr()` and `.to_char()` to the
  canonical `rt_char_from_code` ABI, which `runtime_native.c` exports. The
  retired `text_dot_from_char_code` reference proves the deployed stage2 compiler
  predates that lowering. Reusing that compiler is not a valid verification run.
- The TCP names were stale class-symbol spellings and are covered by the same
  artifact rejection list until a fresh compiler proves the canonical aliases.

## Gate

Use `scripts/check/build-simple-web-server-native.shs`. It clears bootstrap and
runtime-path overrides, sets `SIMPLE_NO_STUB_FALLBACK=1`, builds the complete
entry closure with the current compiler sources, rejects unresolved-stub output,
and rejects the exact six symbols if any survives in the executable.

Do not add compatibility zero/nil bodies and do not treat the prior linked
artifact as evidence. Acceptance requires this gate to pass, followed by the
bounded live listener/HTTP smoke.
