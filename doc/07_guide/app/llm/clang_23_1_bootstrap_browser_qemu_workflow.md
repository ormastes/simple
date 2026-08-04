# Clang 23.1 Bootstrap, Browser, and QEMU Workflow

Use this bounded workflow when changing the pure-Simple LLVM backend or the
SimpleOS compiler/browser lane. Run each unchanged gate once and retain its
command, log, tool versions, and artifact SHA-256. After a failure, make one
evidence-driven fix and rerun only the affected gate. Stop after three
verify/fix cycles and report the concrete blocker; never loop a passing or
identically failing command.

## 1. Build and admit the provider

Stable LLVM 23.1 is not yet published. The repository pins the signed upstream
`llvmorg-23.1.0-rc2` tag and verifies its Git signature before building:

```bash
sh scripts/setup/build-llvm-23-1-provider.shs \
  --source-dir build/toolchains/llvm-project-23.1.0-rc2 --clone --jobs 8
export LLVM_23_1_PREFIX="$PWD/build/toolchains/llvm-23.1.0-rc2"
export SIMPLE_LLVM_PREFIX="$LLVM_23_1_PREFIX"
sh scripts/setup/build-llvm-23-1-provider.shs \
  --source-dir build/toolchains/llvm-project-23.1.0-rc2 --verify-only
```

`LLVM_23_1_PREFIX` configures shell producers; `SIMPLE_LLVM_PREFIX` configures
the pure-Simple backend. Admission requires one prefix containing the coherent
nine-tool family: `clang`, `ld.lld`, `llc`, `opt`, `llvm-ar`, `llvm-nm`,
`llvm-objdump`, `llvm-objcopy`, and `llvm-config`. Preserve the builder's exact
absolute handoff metadata and export it without PATH-based substitutions:

```bash
export SIMPLE_LLVM_PREFIX="$LLVM_23_1_PREFIX"
export CLANG="$LLVM_23_1_PREFIX/bin/clang"
export SIMPLE_CLANG="$CLANG"
export LINKER="$LLVM_23_1_PREFIX/bin/ld.lld"
export SIMPLE_LINKER="$LINKER"
export LLC="$LLVM_23_1_PREFIX/bin/llc"
export SIMPLE_LLC="$LLC"
export OPT="$LLVM_23_1_PREFIX/bin/opt"
export SIMPLE_OPT="$OPT"
export LLVM_AR="$LLVM_23_1_PREFIX/bin/llvm-ar"
export SIMPLE_AR="$LLVM_AR"
export LLVM_NM="$LLVM_23_1_PREFIX/bin/llvm-nm"
export SIMPLE_NM="$LLVM_NM"
export LLVM_OBJDUMP="$LLVM_23_1_PREFIX/bin/llvm-objdump"
export SIMPLE_OBJDUMP="$LLVM_OBJDUMP"
export LLVM_OBJCOPY="$LLVM_23_1_PREFIX/bin/llvm-objcopy"
export LLVM_CONFIG="$LLVM_23_1_PREFIX/bin/llvm-config"
```

The Rust in-process LLVM Cargo feature is a different boundary: current
vendored `inkwell`/`llvm-sys` bindings stop at LLVM 18.
`LLVM_SYS_180_PREFIX` is legacy Rust-only and must remain isolated from every
23.1 variable above. It is not a migration path or production fallback. The
canonical Rust bootstrap is Cranelift-only and rejects `--backend=llvm` or
`--backend=llvm-lib` before Cargo runs:

```bash
sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --full-bootstrap --backend=cranelift --mode=dynload
```

Only the resulting current-source pure-Simple compiler may consume the
admitted 23.1 provider for LLVM native builds.

## 2. Admit Stage 2, Stage 3, and the current-source Stage 4 full CLI

Each stage is a provider for one narrower handoff:

| Artifact | Required admission | Permitted use |
|---|---|---|
| Stage 2 `build/bootstrap/stage2/<triple>/simple` | Built by the current Rust seed, private copy unchanged, bootstrap compiler sanity passes | Produce and sanity-check Stage 3 only |
| Stage 3 `build/bootstrap/stage3/<triple>/simple` | Built by admitted Stage 2 without Rust native-build delegation; `stage3/<triple>/provenance.env` re-verifies and sanity passes | Produce Stage 4 only |
| Stage 4 `build/bootstrap/full/<triple>/simple` | Built by admitted Stage 3; source fingerprint, sibling `simple.provenance.env`, redeploy gate, frontend gate, and essential-tools smoke all pass | Launch browser builders and the production QEMU rendering wrapper |

Produce the full chain with stub fallback disabled. The Rust seed remains
Cranelift-only; the admitted Stage 4 full CLI consumes the external LLVM 23.1
provider later when the browser and SimpleOS LLVM lanes run:

```bash
SIMPLE_NO_STUB_FALLBACK=1 \
sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --full-bootstrap --backend=cranelift --mode=dynload --full-cli --no-mcp
```

If Stage 3 fails, retain its cache and provenance/log directory and repair that
failure; do not skip directly from Stage 2 to the QEMU wrapper. If Stage 4
fails, retain the Stage 2/3 artifacts as producer evidence but do not relabel
either one as a full CLI.

The qualifying producer is `build/bootstrap/full/<triple>/simple` from the
current source revision. Retain its absolute path, source revision, version,
SHA-256, and sibling `.provenance.env`, then run
`scripts/check/check-bootstrap-essential-tools-smoke.shs` once against that
exact binary with stub fallback disabled. The gate must prove its calibrated
test runner, lint, duplicate-check, and aggregate pass markers before QEMU.

An ad-hoc `build/native_probe/simple` can provide diagnostic native-smoke
evidence only. A passing probe proves that artifact can compile and execute the
focused native fixtures; it does not prove the full CLI command surface,
current-source Stage 3 parentage, or the Stage 4 essential-tools gate. Stage 2
and Stage 3 artifacts, the Rust seed, a deployed stale wrapper, or a candidate
without current-source provenance and essential-tools PASS may not substitute
for Stage 4. For a diagnostic native smoke:

```bash
SIMPLE_BINARY="$PWD/build/native_probe/simple" \
SIMPLE_NO_STUB_FALLBACK=1 \
SIMPLE_LLVM_PREFIX="$SIMPLE_LLVM_PREFIX" \
NATIVE_SMOKE_BACKEND=llvm \
NATIVE_SMOKE_WORK_DIR="$PWD/build/clang-23.1-native-smoke" \
sh scripts/check/native-smoke-matrix.shs
```

Acceptance of this diagnostic requires `native_smoke_matrix=true`, no fallback
diagnostic, and successful execution of the produced probes. It does not
promote the artifact to Stage 4. Preserve the work directory and logs when the
smoke fails.

## 3. Build the browser guest payload

Build with the same admitted compiler, linker, and archiver family:

```bash
LLVM_23_1_PREFIX="$LLVM_23_1_PREFIX" \
SIMPLE_LLVM_PREFIX="$SIMPLE_LLVM_PREFIX" \
CLANG="$LLVM_23_1_PREFIX/bin/clang" \
SIMPLE_CLANG="$LLVM_23_1_PREFIX/bin/clang" \
LINKER="$LLVM_23_1_PREFIX/bin/ld.lld" \
SIMPLE_LINKER="$LLVM_23_1_PREFIX/bin/ld.lld" \
LLC="$LLVM_23_1_PREFIX/bin/llc" \
SIMPLE_LLC="$LLVM_23_1_PREFIX/bin/llc" \
OPT="$LLVM_23_1_PREFIX/bin/opt" \
SIMPLE_OPT="$LLVM_23_1_PREFIX/bin/opt" \
LLVM_AR="$LLVM_23_1_PREFIX/bin/llvm-ar" \
SIMPLE_AR="$LLVM_23_1_PREFIX/bin/llvm-ar" \
LLVM_NM="$LLVM_23_1_PREFIX/bin/llvm-nm" \
SIMPLE_NM="$LLVM_23_1_PREFIX/bin/llvm-nm" \
LLVM_OBJDUMP="$LLVM_23_1_PREFIX/bin/llvm-objdump" \
SIMPLE_OBJDUMP="$LLVM_23_1_PREFIX/bin/llvm-objdump" \
LLVM_OBJCOPY="$LLVM_23_1_PREFIX/bin/llvm-objcopy" \
LLVM_CONFIG="$LLVM_23_1_PREFIX/bin/llvm-config" \
sh scripts/os/build_browser_demo_client.shs
```

Retain `build/os/apps/browser_demo/browser_demo.elf`, its SHA-256, and the
builder output. A host ELF, placeholder payload, mismatched LLVM family, or
missing `x86_64-unknown-simpleos` ELF admission is a failure.

## 4. Run the canonical SimpleOS rendering gate

The fullscreen wrapper rebuilds and stages the browser as
`/SYS/APPS/BROWSMF.SMF`, defaults its native kernel build to LLVM, boots QEMU,
and validates framebuffer, font, keyboard, pointer, and browser-content
evidence. Pass the exact admitted Stage 4 binary and all provider owners
explicitly; do not rely on the wrapper's artifact search or host PATH:

```bash
SIMPLE_BIN="$PWD/build/bootstrap/full/<triple>/simple" \
SIMPLEOS_WM_NATIVE_BACKEND=llvm \
LLVM_23_1_PREFIX="$LLVM_23_1_PREFIX" \
SIMPLE_LLVM_PREFIX="$SIMPLE_LLVM_PREFIX" \
CLANG="$LLVM_23_1_PREFIX/bin/clang" \
SIMPLE_CLANG="$LLVM_23_1_PREFIX/bin/clang" \
LINKER="$LLVM_23_1_PREFIX/bin/ld.lld" \
SIMPLE_LINKER="$LLVM_23_1_PREFIX/bin/ld.lld" \
LLC="$LLVM_23_1_PREFIX/bin/llc" \
SIMPLE_LLC="$LLVM_23_1_PREFIX/bin/llc" \
OPT="$LLVM_23_1_PREFIX/bin/opt" \
SIMPLE_OPT="$LLVM_23_1_PREFIX/bin/opt" \
LLVM_AR="$LLVM_23_1_PREFIX/bin/llvm-ar" \
SIMPLE_AR="$LLVM_23_1_PREFIX/bin/llvm-ar" \
LLVM_NM="$LLVM_23_1_PREFIX/bin/llvm-nm" \
SIMPLE_NM="$LLVM_23_1_PREFIX/bin/llvm-nm" \
LLVM_OBJDUMP="$LLVM_23_1_PREFIX/bin/llvm-objdump" \
SIMPLE_OBJDUMP="$LLVM_23_1_PREFIX/bin/llvm-objdump" \
LLVM_OBJCOPY="$LLVM_23_1_PREFIX/bin/llvm-objcopy" \
LLVM_CONFIG="$LLVM_23_1_PREFIX/bin/llvm-config" \
BUILD_DIR="$PWD/build/clang-23.1-simpleos-wm-evidence" \
REPORT_PATH="$PWD/doc/09_report/clang_23_1_simpleos_wm_evidence.md" \
sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs
```

Only the wrapper's retained report and evidence bundle can establish the QEMU
rendering result. Static contracts, a browser ELF alone, cached screenshots,
an unavailable QEMU run, or a Stage 2/3 substitution do not constitute a live
PASS. Verify each unchanged criterion once. After each failure make at most one
focused fix, and stop with retained blockers after the third verify/fix cycle.
Until such a retained bundle reports PASS, describe the lane as pending or
blocked; a native-probe smoke result must never be summarized as a QEMU render
success.

## Related guidance

- [Compiler build and provider setup](../../compiler/build.md)
- [Multiarch QEMU systest guide](../../os/multiarch_qemu_systest_guide.md)
- [Bootstrap and binary architecture](../../../../.claude/rules/bootstrap.md)
