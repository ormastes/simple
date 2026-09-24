# arm64 Stage2→Stage3 production retry

- Source head: `559b6808ede`
- Producer wiring commit present: `777cf9ad5a3`
- Admitted parent: `/Users/ormastes/simple/bin/release/macos-arm64/simple`
- Parent SHA-256: `277f8ac9e14ae266ce380a5890d434ce27b47cee9378e2b337cbcc8cd4086767`
- Stage2 producer invocation count: exactly one
- Exit status: `1`
- Verdict: blocked before Stage2 compilation

The disk-space preflight passed. The next authority preflight refused because
this integration checkout contains none of the authenticated runtime tuple:

```text
src/compiler_rust/target/bootstrap/simple
src/compiler_rust/target/bootstrap/libsimple_native_all.a
src/compiler_rust/target/bootstrap/libsimple_compiler_backfill.a
```

The pure-Simple executable is independently admitted, but its provenance does
not authenticate replacement runtime archives or a hosted-runtime receipt.
Generating those receipts from paths, borrowing unrelated cache archives, or
copying a standalone binary would synthesize authority. Rebuilding the tuple
through `--full-bootstrap` would use the Rust seed. All are forbidden by the
requested constraints, so no source change safely removes this prerequisite.

No Stage2 artifact, Stage2 parent receipt, planner admission, or Stage3 process
was created. The exact stdout, stderr, environment, progress records, and exit
status are retained with this verdict.
