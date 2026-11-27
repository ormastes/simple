# Hosted native link never requests SDL2 unconditionally

Requirement: REQ-SSPEC-COMPILER — regression guard for
`linux_native_link_unconditional_lsdl2_2026-09-06`.
Executable source: test/01_unit/compiler/backend/linker/no_unconditional_sdl2_link_spec.spl.
Three scenarios, zero placeholders.

| Scenario | Fixture | Expected result |
|---|---|---|
| Linker wrapper scan | every line containing `SDL2` in `native_linking.spl` | comment line only (no active push) |
| Support-args table scan | every line containing `SDL2` in `native_all_support.spl` (linux/freebsd/macos arms) | comment line only |
| Explicit request path | `config.libraries` loop in `native_linking.spl` | still present |

The hosted link paths used to push `-lSDL2` unconditionally, so `native-build`
failed at the link step on any host without the SDL2 dev package (under
`--as-needed` the linker must still FIND libSDL2). The repair removes the
unconditional push from every OS arm: `src/runtime/runtime_sdl2.c` binds SDL
through dlopen/dlsym at first use, the runtime archive carries zero undefined
`SDL_*` symbols, and a program that wants SDL2 linked statically requests it
via `config.libraries`. The previously "untouched and still suspect" macOS
and FreeBSD arms now carry the same exclusion in the shared table.

Discrimination evidence: injecting an active `args.push("-lSDL2")` line into
`native_linking.spl` fails scenario 1; with the source as landed, 3/3 pass.

Reproduce with the admitted self-hosted runtime once deployed:

```bash
bin/simple test test/01_unit/compiler/backend/linker/no_unconditional_sdl2_link_spec.spl --mode=interpreter
```

Current-session evidence (Rust seed interpreter, aarch64 Linux host, no SDL2
dev package installed):
`outcome=OK declared>=3 executed=3 passed=3 failed=0 skipped=0 dropped=0`.
