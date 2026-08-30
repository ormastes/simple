# Stage 4 bootstrap blocked by zerocopy vendor checksum mismatch

**Status:** claimed for the frozen Stage-4 transaction. **Observed:**
2026-08-15.

Cycle 2 passed the bootstrap reason-receipt guard and began the Rust authority
build, then Cargo exited 101 before Simple source discovery. The exact first
diagnostic was:

```text
error: the listed checksum of `src/compiler_rust/vendor/zerocopy/win-cargo.bat` has changed
expected: 5da2a90a04a60728fcd0b35d3657ec1441ea22f4f47ab1d73b55e59b34adc65a
actual:   dbde5af501630f6d14a0681d27f30ef2ffaeb1753d14be2f7cb1a7f285458c07
```

The working file is clean at the frozen HEAD and its SHA-256 exactly matches
the `zerocopy-0.8.33.crate` archive already present in the local Cargo cache.
The defect is therefore the stale `.cargo-checksum.json` entry, not a modified
third-party source file. The scoped fix updates that one checksum token to the
actual upstream archive hash. Cycle 2 processed zero Simple files and zero
Simple modules; elapsed time was 17.48 seconds and peak RSS was 153,120 KiB.
