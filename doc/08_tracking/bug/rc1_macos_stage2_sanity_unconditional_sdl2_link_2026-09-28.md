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

On this Mac, an isolated `cargo check --release --locked --offline --bin simple`
passed, followed by one `cargo build --release --locked --offline --bin simple`
with `CARGO_BUILD_JOBS=2`. The build completed in 5m 47s and produced a 35 MiB
Rust bootstrap seed with SHA-256
`2e6639df852eeded2db03d38e4f6496e4d332c1b5b00036add678aea6ad63d20`.
It reports `Simple Language v1.0.0-rc.1` with the explicit seed warning.
The build used the local RC1 source at `636c057e315`; the later protected
release tip `6f96848e395` changes only
`.github/release-convergence-manifest.json` relative to that base. This proves
Stage 1 can build on this macOS host, not that the Linux candidate's exit 101
is fixed, nor that Stage 2/3 bootstrap or this linker change passes.

The local repair branch was rebased onto protected `release/1.0` tip
`7fbcd449abba86176b48c8c534713c7134b7067a` on 2026-09-28. The rebased
diff remains limited to this note, the linker, and its focused spec. The
earlier Rust seed build is historical evidence for the older source identity;
it does not certify this newer tip. Main macOS Phase 2/3 run `36370942485`
was still pending with no assigned job at this check. The same host had 6.7
GiB free, still below the 20 GiB bootstrap preflight floor.
