# Windows Stage 2 cache resume rejects canonical executable paths

Status: fixed in the resume wrapper; platform fixture passes. Actual compiler
admission remains the responsibility of the canonical bootstrap replay.

The retained run `build/bootstrap/runner-sosix-stage2-current-tools` records
`stage2/x86_64-pc-windows-msvc/simple.exe` as its output and
`stage3/x86_64-pc-windows-msvc/stage2-runtime-authority/simple.exe` as its
executable. Its rejected linked candidate is not admitted compiler evidence.
The wrapper compared both paths against extensionless `simple`, refusing with
`transcript output path is not canonical` before cache replay.

The constructor already uses `.exe` for Windows. The wrapper now derives the
suffix from the host triple for Windows MSVC and GNU, applying it to canonical
output, admitted output, frozen compiler existence and transcript executable
identity. POSIX remains extensionless. No transcript, candidate or admission
check is rewritten or relaxed.

Regression: `sh scripts/check/check-bootstrap-stage2-resume-platform.shs`
passed 24 cases on native Windows MSYS Bash. It executes production validation
with real directories and length-prefixed transcripts for MSVC, GNU Windows,
Linux and Darwin; rejects wrong output/compiler suffixes, absent compiler, and
existing canonical/admitted outputs. This fixture does not claim compilation,
sanity, cache-clone or admission success.

Continuation instructions: [Stage 2 cache resume](../../07_guide/tooling/stage2_cache_resume.md).
