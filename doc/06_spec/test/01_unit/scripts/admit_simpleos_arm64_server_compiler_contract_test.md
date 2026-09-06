# Admit SimpleOS ARM64 server compiler

The producer accepts only an undeployed full Stage4 CLI with its canonical
sibling provenance. It reruns the essential-tools gate and invokes the
canonical ARM64 server-payload builder exactly once. That build uses
`aarch64-unknown-simpleos`, the ARM64 sysroot, the SimpleOS runtime archive,
and `SIMPLE_NO_STUB_FALLBACK=1`. The resulting ELF is checked and hashed but
never executed on the host.

Run the architecture-safe negative contract check with:

```sh
sh test/01_unit/scripts/admit_simpleos_arm64_server_compiler_contract_test.shs
```

The self-test deliberately supplies malformed synthetic provenance. Success
means the producer rejected it, published no receipt, and left no staged
receipt. It also proves an output parent containing a symlink is rejected
without mutating the symlink target. Synthetic inputs can never produce a
passing admission.

A live invocation is:

```sh
sh scripts/check/admit-simpleos-arm64-server-compiler.shs \
  --compiler build/bootstrap/full/x86_64-unknown-linux-gnu/simple \
  --provenance build/bootstrap/full/x86_64-unknown-linux-gnu/simple.provenance.env \
  --output build/test-artifacts/simpleos-arm64-server-compiler-admission/receipt.env
```

On success the mode-`0600` receipt binds HEAD, the dirty-inclusive QEMU source
manifest, compiler path/version/hash, canonical Stage4 provenance, Stage4 log
hashes, and the newly executed essential/native smoke log hashes. Any identity
change removes the candidate receipt and fails closed.

The output parent is canonicalized below the real
`build/test-artifacts` directory before mutation; traversal and symlink
components are rejected. Smoke logs may be moved into place first, but the
mode-`0600` receipt rename is the final publication action. Until that rename
completes and `published=1` is set, the exit/signal trap removes the final
receipt and published logs.
