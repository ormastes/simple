# Windows CI seed crashes before command dispatch

## Reproduction and cause

Build Binaries run `45199934467`, job `137780553342`, built release
`d89f975af3cb46782e0c1dd68a795bb5833da846`. Artifact `14830379485`
(`seed-mingw-x86_64-d89f975af3cb46782e0c1dd68a795bb5833da846`) passed the
old file-presence check but its executable faults on native Windows `--version`.
The archive SHA-256 is
`abbde161d196b68eea71a553db7253bcebd3268949b8ad14c429f1f025c1df1d`.

One bounded CDB launch captured an access violation in `mi_malloc_aligned`,
called through Rust allocation during `register_static_runtime_symbols`
constructor initialization, before main. A HIGHLOW base relocation at RVA
`0xE4E375` changes the TLS displacement of the instruction at RVA `0xE4E372`
from `0x136a0` on disk to `0xa9cf36a0` at image base `0x7ff6e9ce0000`.
The low relocation delta is `0xa9ce0000`, exactly accounting for the corruption.
This is independent of the hosted compiler link dispatch repaired by #11103.

The old Ubuntu job selected clang for C compilation only; it did not select
the Cargo Windows final-link driver. It used the unpinned nightly GNU target,
and never executed Windows seeds before publishing them.

## Repair and acceptance boundary

The Windows seed now builds on hosted Windows using the existing pinned
LLVM-MinGW UCRT installer and bootstrap's pinned gnullvm Rust host. Both native
C compilation and Cargo final linking select that same driver and its CRT
directory, with the GNU target and LLD. The Linux compiler stages remain intact.
No executable rewriting or security-feature disabling is involved.

`check-seed-startup.py` executes the exact output with `--version`, bounds it to
30 seconds, requires zero exit and Simple identification, checks its hash remains
unchanged, and retains a JSON receipt even on process failure or timeout.
Publication cannot proceed after failure. The receipt proves startup only,
not Hello compilation, runtime compatibility, or bootstrap admission.

`python scripts/check/check-seed-startup-test.py` compiles one small native C
fixture using `CC` (or clang) and verifies success, nonzero exit, wrong output,
and timeout against real processes. This fixture is not a compiler substitute.
The Windows fixture regression passed with the pinned LLVM-MinGW driver.

Actual repaired CI compiler startup remains a required post-build result; the
local fixture test does not claim it. Original debugger and artifact evidence is
retained externally under
`D:/dev/simple-user-storage/build/release-bootstrap-20261123/ci-d89f975-windows-host`.
