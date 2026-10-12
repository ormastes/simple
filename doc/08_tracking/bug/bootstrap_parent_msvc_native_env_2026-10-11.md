# Admitted-parent refresh omitted the MSVC native environment

REQ-PARENT-MSVC-ENV: an admitted pure-Simple parent and a full bootstrap must
construct the same canonical Stage2 MSVC environment, with an admitted C
compiler, quoted SDK paths, and an explicit empty LIBPATH when appropriate.

Attempt05 refused before executing any compiler. Its refusal log at
`rp3e-20261011/logs/x86_64-pc-windows-msvc/stage2-native-build.log.refusal`
reported precisely four missing assignment names: CC, INCLUDE, LIB, LIBPATH.
The script initialized all four internal assignment variables to empty, then
populated them only inside `full_bootstrap=1`. An admitted-parent refresh skips
that Rust-specific branch. Caller exports cannot repair reset internal state;
the Stage2 argument builder's conditional expansions omitted all four names.

Move the existing MSVC assignment block into shared native-stage setup before
seed fingerprinting. Resolve CC through the existing canonical target C
compiler validator. Preserve separate quoted words, including literal
`LIBPATH=`. The full-build LLVM authority may still replace the initial C
driver with its exact pinned physical clang-cl path. No canonical name list,
receipt verifier, Rust prerequisite, or parent admission check is weakened.

Validation: `bootstrap_parent_msvc_env_test.shs` passed once under WSL. It
extracts the real shared setup, real Stage2 argument construction, and real
LLVM override. Parent and full routes match the production canonical names;
compiler and SDK paths retain spaces/semicolons; empty LIBPATH remains present;
an invalid compiler fails closed. This is controlled shell contract evidence,
not native compilation. No frozen source, live receipts or caches were changed
during implementation; reviewed transport precedes any next attempt.
