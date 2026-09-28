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

An earlier `main` fix, `8733526cf8f0d49562cd5e8617533c761243fcc6`,
cherry-picks cleanly to RC1 as `27df83e1c399fbd02a625a2f3484b05ae651bd56`.
The changed lines have the same zero-context stable patch ID
`a6122a3e65a534d455093cd2c7e79a7ceeef402e`. The release gate uses
standard `git show | git patch-id --stable`: source is
`ec74df8428714a62d30c7c58879f1c1af54b87ca`, result is
`d9ceb64fefc1fd37ee24a13c626dfaaff682fa2e`. The earlier fix also leaves
macOS `-lc/-lpthread/-lm` on the RC1 link line. It is not a complete macOS
bootstrap repair or an admissible exact backport.

The focused spec is in
`test/01_unit/compiler/linker/native_link_hardening_spec.spl`. The local July
beta self-hosted binary could not run it: parsing unrelated current source
`module_surface_types.spl` failed before test assertions. A current RC1
bootstrap must run the spec and the full macOS Phase 2/3 evidence gate.
On 2026-09-28 the local APFS data volume had 7.4 GiB free; the repository's
bootstrap preflight requires 20 GiB. No full local bootstrap was started with
insufficient space. The `main` macOS CI run `36369147089` was pending with no
job assigned when first checked, then was cancelled by a newer push. Run
`36370136718` was pending with no job assigned when checked afterward; no
successful full macOS Phase 2/3 evidence was available.

The same day's [RC1 candidate a006](https://github.com/ormastes/simple/actions/runs/36370043783)
failed earlier on Linux while building the Rust seed (`rust-seed-build` exit
101), before Stage 2 or any macOS linker check. The job only named its private
`rust-seed-build.log`; it uploaded no artifact containing that log. This is an
independent release gate and cannot be counted as evidence for this linker fix.
