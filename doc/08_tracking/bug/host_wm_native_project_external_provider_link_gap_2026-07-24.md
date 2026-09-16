# Host WM Native-Project External Provider Link Gap — 2026-07-24

## Status

Source fixed; fresh bootstrap and production recapture required.

## Observed failure

The exact-current pure-Simple Stage 3 compiler
`6c64561afe77b4453cdc7662643c2b767b26e8182e37c917df6a3a39a8b4e754`
was accepted by the production host WM gate. The native artifact then failed
to link because the native-project linker ignored `SIMPLE_LINK_OBJECTS`.
Unresolved symbols included the real winit event/window API, Vulkan runtime
providers, and `rt_write_u32s_to_raw`.

The generic native linker already consumed the same environment contract.
The native-project linker did not, creating two incompatible native-build
behaviors.

## Root fix

`src/compiler_rust/compiler/src/pipeline/native_project/linker.rs` now:

- parses provider paths with platform path-list semantics;
- rejects missing/non-file providers;
- adds providers to the final native-project link command;
- includes providers in unresolved-symbol analysis so strict builds do not
  synthesize duplicate stubs.

The focused Rust regressions pass: `3 passed; 3348 filtered out`. They cover
platform path-list parsing, missing-provider rejection, a real dynamic provider
link/run, and suppression of a duplicate unresolved-symbol stub.

The production wrapper also now ships the two bridge builders it referenced:

- `scripts/build/build_spl_winit.shs`
- `scripts/build/build_simple_runtime_sffi.shs`

Both builders stage `@rpath` dynamic providers, and the wrapper passes them
through `SIMPLE_LINK_OBJECTS`. The native-project linker adds provider
directories to the executable rpath. The wrapper rejects missing load commands
and launches without `DYLD_INSERT_LIBRARIES`.

## Cycle accounting

The three permitted host cycles are exhausted:

1. fail before launch: referenced bridge-build scripts were missing;
2. fail before launch: providers built, but native-project link ignored them;
3. same link boundary confirmed after wrapper wiring.

No fourth host launch is permitted in this session. The next session must
bootstrap the compiler containing this fix, then run the production host gate
once. No screenshot or runtime PASS exists yet.
