# Windows GNU bootstrap native-tool fingerprint instability

Date: 2026-09-26

Status: Fix implemented; canonical Stage-2 verification pending

## Symptom

The canonical Windows-GNU bootstrap reaches successful cached builds for the
Rust seed, `simple-native-all`, the no-LTO runtime, and compiler backfill, then
refuses authority publication because the pre- and post-build input
fingerprints differ:

```text
error: Rust inputs changed during full bootstrap; refusing to publish a stale seed
VERDICT — ABORTED: stage=rust-rust-compiler-backfill-build exit=1
```

All source/policy/toolchain categories are byte-identical. Only
`category_native_tools_sha256` alternates:

- pre-build: `e77382517e3d05298292bf89b00cd57434435fb4da86024da3bbedfd973be792`
- post-build: `e4e31d8b89f7b6ba1cf4b1fec91cd2c475d5ef663434949802f8bc8e242f85a5`

The trace also records intermittent native process launch status 125 for
`rustc-sysroot`, `rustc-fingerprint-version`, and `cargo-version`. A bounded
Windows `.exe` metadata retry (four attempts, with binary hashes checked before
and after every launch) was added and its focused unit test passes. A retained
standalone fingerprint using the exact canonical environment matches the
preserved pre-build aggregate, proving the tool bytes and source inputs are
stable.

The remaining mismatch was self-induced by the fingerprint implementation:
the C-compiler `--version` observation used a one-shot `env -i` launch and
recorded nonzero launch status as valid fingerprint data. A transient 125 could
therefore produce a different, apparently valid native-tool category after
Cargo. The C probe now uses the same byte-pinned bounded metadata helper as
Rust and LLVM. Persistent failure aborts fingerprinting; it can no longer be
published as a different authority. The focused native-tool regression passes.

## Reproduction

```powershell
$env:SIMPLE_WINDOWS_ABI='gnu'
$env:SIMPLE_LINKER_FLAVOR='gnu'
sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap `
  --stop-after-stage2 --strategy=normal --backend=cranelift `
  --output=build/mold-linker/bootstrap-stage2-gnu --no-mcp `
  --progress=build/mold-linker/bootstrap-stage2-gnu-progress.log
```

Evidence is retained under
`build/mold-linker/bootstrap-stage2-gnu/`, including
`rust-authority-fingerprint-current.details.env` and the four Rust build logs.
The first stale staging generation was preserved as
`src/compiler_rust/target/bootstrap.generations/.orphaned-43bf43a08fee8e8142cbb64836f62b97`.

## Remaining verification

Complete the canonical Stage-2 bootstrap in a fresh recovery allowance and use
the admitted artifact for linker specs. The details sidecar now emits ordered
per-record native-tool hashes, and the diff tool can retain current details and
error traces for any recurrence. Do not bypass or manually publish a failed
authority.
