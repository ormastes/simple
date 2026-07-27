# Test-host artifact symlink revalidation

`test_host_env` re-hashes retained RenderDoc and framebuffer artifacts through
`file_exists`/`file_hash_sha256`, which follow symlinks. Replacing a previously
valid artifact with a symlink to identical bytes can therefore preserve a PASS
even though the producer rejects symlinks.

## Required fix

Add a real app-I/O no-follow regular-file query backed by runtime `lstat` (not
the current mock `file_is_symlink`), then require it before every retained-file
rehash in `src/app/test/test_host_env.spl`. Add focused same-bytes symlink
mutations for RenderDoc `.rdc`/XML and framebuffer PPM bindings.

## Resolution

Implemented `file_is_regular_no_follow` in the canonical file-ops owner with
POSIX, Windows, Rust-native, and interpreter runtime support. `test_host_env` now requires it
for the RenderDoc capture/XML and baseline/input framebuffer PPMs before
re-hashing. Focused tests use same-byte symlinks so hash equality alone cannot
pass.

The check-then-hash sequence still has a TOCTOU ceiling. If retained artifacts
become writable by a hostile concurrent process, replace it with a no-follow
open/fstat/hash-on-fd operation.

## Postponed environment proof

- Windows source uses UTF-8-to-UTF-16 conversion and rejects reparse points, but
  this Linux session has no admitted Windows test host. Run the focused file-ops
  and `test_host_env` specs on Windows before claiming native Windows PASS.
- The standalone pure-Simple `simple_core` archive has no stable file-type
  primitive. Add a target-owned no-follow metadata ABI before exporting this
  facade there; do not guess `struct stat` layouts or treat `fopen` as proof.
