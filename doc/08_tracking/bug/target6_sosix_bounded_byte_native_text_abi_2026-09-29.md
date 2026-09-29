# Target 6 Sosix bounded byte read: native text ABI omission (2026-09-29)

Status: pure-Simple ABI registry corrected; native retest pending.

The cold native object persistence bridge now imports the narrow hosted Sosix
`bounded_file` facade instead of importing the lower-level file library. A
19-unit no-stub native facade probe built successfully, and its text read of
its own regular fixture passed. The byte read of the same path and bound
returned `regular no-follow bounded file read failed (bad arguments)`.

The C byte reader takes `(const uint8_t* path_ptr, uint64_t path_len,
int64_t max_bytes)` and rejects an invalid path or length with that error.
Both Rust codegen text-argument registries already split its path into
`(ptr, len)`. The pure-Simple `text_arg_indices` registry omitted this byte
reader while registering its text sibling. That omission makes native calls
pass the wrong ABI shape. The pure-Simple registry now includes the byte
reader, and `path_extern_abi_agreement_spec.spl` pins agreement with the C
declaration and Rust registry.

The diagnostic facade probe reached the session's three-cycle verify/fix cap
before the ABI correction. Its existing executable was built by the older
compiler, so another run of it cannot verify the correction. Rebuild the
probe with a compiler containing this registry change and check bounded,
symlink, and binary-success arms in the next scoped verification session.
Until then, do not claim the Sosix native byte path or Target 6 cutover PASS.
