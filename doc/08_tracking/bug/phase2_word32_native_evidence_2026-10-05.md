# Phase 2 native word32 bitmap semantics evidence

Status: native word semantics passed; vector execution and the full goal remain unqualified.

`test/04_smoke/bitmap_word32_native.spl` is the exact source compiled and
executed with the repaired Linux Phase 2 compiler. It checks unsigned
32-bit AND/OR against an independent arithmetic bit oracle, including the
high bit, all ones, alternating bits, empty arrays and lengths around
16/32/64-word boundaries. Six input rotations produce 4044 comparisons.
Length mismatches, value mismatches and an unexpected comparison count fail
the executable.

Recorded source SHA256:
`55fa85adb4ed062c2111ddf64bbe523d755e257ea6e7e474137d584102ecc215`.
The Phase 2 compiler SHA256 is
`b0fccf9f6667808acbb01bee6dbeaa53f3d0038e31068f9aeee58a21c6b4a53e`;
it was built from release `f21317acc86ad9ada43023328173b9283fa9a24a`
plus the byte-fingerprint repair subsequently merged through PR #2570.
It passed the canonical Hello compile-and-execute gate before this test.

The LLVM native build and executable both exited zero. Compiler process-tree
peak RSS was 2723584 KiB under an enforced 5859375 KiB cap. The test run
peaked at 8080 KiB under an enforced 1000000 KiB cap. Both resource receipts
record completion and quiescence. The native executable SHA256 is
`2261c214feedead1073b73bb5ffeed2ea46b02c039db23464b05823b4fa3eed2`.

Actual stdout:

```text
WORD32_NATIVE_PASS checks=4044
avx512_execution_attestation=unproved
```

The isolated WSL checkout `/var/tmp/simple-item5-phase2-20261005` retains
`build/item5-word32/build.log`, `build.rss.env`, `run.log`, `run.rss.env`,
the native executable `bitmap_word32_native`, and
`fingerprint-capsule-verification.json` in that directory. The latter also
binds the emitted object to its verified SHA-256 capsule receipt and
byte-identical content-addressed cache object. This landing reuses that
actual successful run; it does not repeat it or imply a new compiler run.

This smoke test proves ordinary native word32 semantics. It does not prove
AVX512 instruction emission or execution, the auto-vectorization rewrite,
DB/web application correctness, or a performance improvement. Those require
their own executable evidence; the user's complete vector goal is not done.
