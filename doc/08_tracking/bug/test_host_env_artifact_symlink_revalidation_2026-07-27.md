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

## Current disposition

Postponed because the required runtime/app-I/O facade is a separate shared
filesystem lane. Current byte revalidation closes deletion and content-tamper
false-greens but is not evidence of no-follow path integrity.
