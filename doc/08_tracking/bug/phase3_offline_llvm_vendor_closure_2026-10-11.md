# LLVM bootstrap offline vendor closure

Status: fixed dependency closure; compiler and Phase 3 qualification pending.

Canonical Windows bootstrap at source
`13ca99671234295dae05e919de105b341870c8ae` passed materialization and native C
admission, then the Rust seed build exited 101 with `no matching package named
llvm-sys found`. The build correctly used `--locked --offline` and the recorded
vendor source replacement. Evidence is retained under
`C:/dev/simple-phase3-bootstrap-evidence`.

Commit `29b578b3c48085bfcc6c8a280cf786674583082d` switched the compiler to the
patched vendored Inkwell and updated Cargo.lock. Its expanded dependency graph
contained 21 registry packages absent from the vendor directory. These include
twelve older optional llvm-sys versions required during Cargo resolution,
alloc-traits, gumdrop and gumdrop_derive, pest, psm, semver and semver-parser,
stacker, and static-alloc. Restoring optional packages does not select their
LLVM features or change the LLVM 23.1 build target.

Generate the locked registry sources in a separate directory with
`cargo vendor --locked --versioned-dirs --manifest-path
src/compiler_rust/Cargo.toml <temporary-directory>`. Copy only missing packages
into the existing vendor tree, preserving patched sources. For each package,
verify its manifest name/version, package checksum against Cargo.lock, and every
file against its Cargo-generated .cargo-checksum.json. Cargo.lock remains
byte-for-byte unchanged.

Validation: `cargo metadata --locked --offline --format-version 1 --features
llvm` succeeds from src/compiler_rust with an empty isolated CARGO_HOME and
the pinned nightly toolchain. This proves dependency resolution without a
registry cache or network. It does not prove Rust compilation, native Stage 2
admission, runner success, or Phase 3 qualification.
