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
the pure-Simple backend. They must identify the same coherent Clang, LLD,
`llvm-ar`, and `llvm-config` 23.1 provider. The Rust in-process LLVM Cargo
feature is a different boundary: current vendored `inkwell`/`llvm-sys`
bindings stop at LLVM 18. `LLVM_SYS_180_PREFIX` is therefore legacy Rust-only,
is not a 23.1 migration path, and must not be used as a production fallback.
The canonical Rust bootstrap is Cranelift-only and rejects `--backend=llvm`
or `--backend=llvm-lib` before Cargo runs:

```bash
sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --full-bootstrap --backend=cranelift --mode=dynload
```

Only the resulting pure-Simple compiler may consume the admitted 23.1
provider for LLVM native builds.

## 2. Admit the ad-hoc pure-Simple candidate

Record `build/native_probe/simple --version` and its SHA-256, then run a
no-stub native smoke against that exact candidate. Do not replace it with the
Rust seed or silently enable fallback:

```bash
SIMPLE_BINARY="$PWD/build/native_probe/simple" \
SIMPLE_NO_STUB_FALLBACK=1 \
SIMPLE_LLVM_PREFIX="$SIMPLE_LLVM_PREFIX" \
NATIVE_SMOKE_BACKEND=llvm \
NATIVE_SMOKE_WORK_DIR="$PWD/build/clang-23.1-native-smoke" \
sh scripts/check/native-smoke-matrix.shs
```

Acceptance requires `native_smoke_matrix=true`, no fallback diagnostic, and
successful execution of the produced probes. Preserve the work directory and
logs when the smoke fails.

## 3. Build the browser guest payload

Build with the same admitted compiler, linker, and archiver family:

```bash
LLVM_23_1_PREFIX="$LLVM_23_1_PREFIX" \
CLANG="$LLVM_23_1_PREFIX/bin/clang" \
LINKER="$LLVM_23_1_PREFIX/bin/ld.lld" \
LLVM_AR="$LLVM_23_1_PREFIX/bin/llvm-ar" \
sh scripts/os/build_browser_demo_client.shs
```

Retain `build/os/apps/browser_demo/browser_demo.elf`, its SHA-256, and the
builder output. A host ELF, placeholder payload, mismatched LLVM family, or
missing `x86_64-unknown-simpleos` ELF admission is a failure.

## 4. Run the canonical SimpleOS rendering gate

The fullscreen wrapper rebuilds and stages the browser as
`/SYS/APPS/BROWSMF.SMF`, boots QEMU, and validates framebuffer, font, keyboard,
pointer, and browser-content evidence. Pass the exact admitted candidate and
provider explicitly:

```bash
SIMPLE_BIN="$PWD/build/native_probe/simple" \
LLVM_23_1_PREFIX="$LLVM_23_1_PREFIX" \
SIMPLE_LLVM_PREFIX="$SIMPLE_LLVM_PREFIX" \
CLANG="$LLVM_23_1_PREFIX/bin/clang" \
LINKER="$LLVM_23_1_PREFIX/bin/ld.lld" \
LLVM_AR="$LLVM_23_1_PREFIX/bin/llvm-ar" \
BUILD_DIR="$PWD/build/clang-23.1-simpleos-wm-evidence" \
REPORT_PATH="$PWD/doc/09_report/clang_23_1_simpleos_wm_evidence.md" \
sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs
```

Only the wrapper's retained report and evidence bundle can establish the QEMU
rendering result. Static contracts, a browser ELF alone, cached screenshots,
or an unavailable QEMU run do not constitute a live PASS.

## Related guidance

- [Compiler build and provider setup](../../compiler/build.md)
- [Multiarch QEMU systest guide](../../os/multiarch_qemu_systest_guide.md)
- [Bootstrap and binary architecture](../../../../.claude/rules/bootstrap.md)
