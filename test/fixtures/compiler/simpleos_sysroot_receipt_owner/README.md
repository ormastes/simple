# SimpleOS SDK owner native bootstrap diagnostic

This imports the production SDK validator and selected-input pre/post owner.
It is an explicit bootstrap diagnostic, not ordinary test execution, SDK/runtime
qualification, a complete target tool build, or suite admission.

The exact retained/fresh P1 compiler may itself have been built by the Rust
seed through the canonical bootstrap pipeline. That P1 provenance is allowed
and must be recorded honestly. Do not invoke an ad-hoc Rust seed for ordinary
test/lint/run commands or present this diagnostic as runtime/suite admission.

After Astra review and verification of the exact fresh P1 artifact, native-build
`main.spl` through that producer with compiler/lib entry closure, isolated cache,
and an output under this checkout's `build/verify`. Record actual producer
identity, source, output hash, compile argv and exit status. No workflow or
producer pin changes are part of this fixture.

Invoke the host wrapper with the absolute compiled executable and its verified
full SHA256; an existing fixture path is deliberately not an accepted argument:

```
sh test/fixtures/compiler/simpleos_sysroot_receipt_owner/run.shs ABS_NATIVE_EXE EXPECTED_SHA256
```

The wrapper clears inherited fixture/target/script/core environment, invokes
`prepare.shs`, then canonicalizes the newly returned path. Its physical parent
must be this checkout's `build/verify`, its basename `sysroot-receipt.*`, and its
`source`/`sdk` children ordinary directories at the expected physical paths.
A fresh run marker is atomically reserved. The probe verifies that marker/path
before mutation. Run cwd is exactly the newly prepared `<fixture>/source`.
Never invoke the raw probe with an arbitrary or reused fixture environment.

`prepare.shs` delegates the unchanged canonical shell fixture owner using
`--fixture-only`: a real Clang ELF32 i686 object, real LLVM archives, complete
nineteen-field SDN receipt and declared ledgers. It duplicates no validator or
builder implementation. Explicit LLVM CC/AR and working MSYS2 shell are needed.

Every successful assertion increments the reported counter. The wrapper retains
separate `bootstrap-owner-run/stdout.log`, `stderr.log` and `result.sdn`; PASS requires executable
exit zero, complete stdout equal to the exact success line (LF or CRLF), and unchanged native
executable hash. It never invokes raw Simple source or falls back to a seed.

Checks include valid real artifacts/receipt acceptance, mutated aggregate and
SDK script rejection by both production owners, arbitrary caller-script
acceptance with distinct ownership, changed actual caller bytes changing the
selected row while preserving SDK identity, and restored original observations.

Status: NOT EXECUTED. Astra review and exact fresh P1 verification precede
compilation/execution. Preparing this fixture is not full SDK qualification.
