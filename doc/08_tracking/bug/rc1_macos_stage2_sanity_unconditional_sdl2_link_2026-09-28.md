# RC1 macOS Stage 2 sanity link requires absent SDL2

- **Source:** `origin/release/1.0` at `636c057e3155d4f76ba635f1b61ed170242f5f16`
- **Observed on main:** [macOS Phase 2/3 run 36355656489](https://github.com/ormastes/simple/actions/runs/36355656489) reached the Stage 2 sanity link and failed with `ld: library 'SDL2' not found`.
- **Release-line status:** Local adaptation prepared; bootstrap and release admission pending.

The RC1 linker has the same unconditional `-lSDL2` in its macOS direct ld64 and
clang fallback paths. Its `runtime_sdl2.c` loads SDL2 dynamically at first use.
The default link should pass `-lSystem` only to direct ld64; clang supplies
libSystem itself. Explicit user libraries remain available through
`config.libraries`.

The release line predates the link-policy table changed by main commit
`a8cb7f5ef4b2a3c4f13c87ec76109cac31284daf`. This adaptation has a different
stable patch ID, so it must not be claimed as an admitted exact backport under
the current reviewed-convergence rule. Obtain a reviewed equivalence path or
make the release-line preimage compatible before candidate admission.

The focused spec is in
`test/01_unit/compiler/linker/native_link_hardening_spec.spl`. The local July
beta self-hosted binary could not run it: parsing unrelated current source
`module_surface_types.spl` failed before test assertions. A current RC1
bootstrap must run the spec and the full macOS Phase 2/3 evidence gate.
