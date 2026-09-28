# macOS Stage 2 sanity link requires absent SDL2

- **Observed:** 2026-09-28 in [macOS Phase 2/3 run 36355656489](https://github.com/ormastes/simple/actions/runs/36355656489)
- **Status:** Link flag fix applied; full Stage 2/3 bootstrap rerun pending

The strict bootstrap built the Stage 2 compiler, then its positional
hello-world native-build failed with `ld: library 'SDL2' not found`. The sanity
gate rejected Stage 2 and did not admit Stage 3 or fall back to the Rust seed.

`native_link_std_lib_args` passed `-lSDL2` unconditionally in both Darwin link
arms. `src/runtime/runtime_sdl2.c` resolves SDL2 with `dlopen` at first use;
its normal runtime archive does not need a link-time SDL2 library. The default
link line now supplies only `-lSystem` to direct ld64 and leaves libSystem to
the clang driver in the compiler-driver fallback. Explicit user libraries
remain available through `config.libraries`.

`test/01_unit/compiler/native/link_line_per_target_spec.spl` checks the Darwin
aliases and all emission sites. A full macOS Phase 2/3 run must pass before this
bug can be marked resolved or macOS bootstrap success claimed.
