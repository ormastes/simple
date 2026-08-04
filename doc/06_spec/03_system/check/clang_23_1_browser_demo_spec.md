# Clang 23.1 Browser Demo Operator Flow

**Executable spec:** `test/03_system/check/clang_23_1_browser_demo_spec.spl`

## Purpose and claim boundary

This manual is for maintainers producing the admitted Clang/LLVM 23.1
provider, pure-Simple compiler, browser client, and SimpleOS QEMU evidence.
The executable spec inspects source contracts; those assertions prove routing,
version policy, and fail-closed ownership, not successful execution on hosts or
targets that were not run.

Current status is **verification-blocked**. In particular, source inspection
must not be promoted to Stage4, essential-tools, cross-host,
multi-architecture, browser-frame, input, or framebuffer PASS evidence.

## Preconditions

- Use one verified `LLVM_23_1_PREFIX` / `SIMPLE_LLVM_PREFIX` containing all
  nine required tools from the same 23.1 provider.
- Use the current signed `llvmorg-23.1.0-rc2` provider until a stable 23.1
  release passes the same admission checks.
- Use a current-source, provenance-verified pure-Simple full Stage4 CLI for
  production LLVM and QEMU gates. Rust seed, Stage2, Stage3, and
  `native_probe/simple` artifacts are diagnostic only.
- Preserve retained logs and hashes. Do not rerun an unchanged acceptance gate
  or exceed three fix/verify cycles.

## Inspect the installed Clang 23.1 toolchain

Set `LLVM_23_1_PREFIX` to an official 23.1 provider. The resolver admits only
one canonical provider prefix containing all nine required executables:
`clang`, `ld.lld`, `llc`, `opt`, `llvm-ar`, `llvm-nm`, `llvm-objdump`,
`llvm-objcopy`, and `llvm-config`. The provider validates every tool as 23.1.0,
checks `llvm-config --prefix` and `--bindir`, and emits canonical handoff
metadata through `SIMPLE_LLVM_PREFIX`, `SIMPLE_CLANG`, `SIMPLE_LINKER`,
`SIMPLE_LLC`, `SIMPLE_OPT`, `SIMPLE_AR`, `SIMPLE_NM`, `SIMPLE_OBJDUMP`, and
`SIMPLE_OBJCOPY` (with `LLVM_CONFIG` for the upstream configuration tool).
Missing, mixed, or falsely labeled families fail closed.

The source-level assertions cover REQ-001, REQ-002, and REQ-007. They do not
replace the retained provider version/hash receipt required by NFR-001,
NFR-006, and NFR-008.

## Build the browser demo with the admitted compiler

Run `scripts/os/build_browser_demo_client.shs`. The admitted Clang compiles both
the browser source and isolated libc; admitted LLD links it. The output must be
an x86-64 ELF with resolved `getpid`. Tool and output hashes are retained in
`build/os/apps/browser_demo/clang-23.1-evidence.txt`. This client build consumes
the compiler/linker/archiver subset of the same nine-tool provider; it does not
create a second or partially admitted toolchain.

The successful client build and ELF/staging evidence cover REQ-003 and the
build portion of REQ-004/REQ-008. Guest execution and correlated browser pixels
remain separate live-evidence obligations.

## Inspect Rust bootstrap isolation

REQ-005 is satisfied by explicit isolation, not by relabeling the legacy Rust
binding. `src/compiler_rust/compiler/Cargo.toml` keeps the optional inkwell 0.5
`llvm18-0` feature outside the default graph. The canonical bootstrap defaults
to Cranelift, rejects `--backend=llvm` with an actionable message, and the
multiplatform bootstrap workflow must neither enable that feature nor provision
LLVM 18.

This proves the permitted non-LLVM bootstrap boundary. It does **not** claim
that Rust inkwell/llvm-sys supports LLVM 23.1. Production LLVM 23.1 begins only
after bootstrap, in the pure-Simple compiler with the admitted external
provider.

## Inspect canonical pure-Simple and guest ownership

REQ-006 source checks cover the pure-Simple runtime compiler, LLVM capability
layer, interpreter LLVM tools, SimpleOS package manifest, image builder, shell
tool aliases, and the focused guest-toolchain contract. They require
`SIMPLE_LLVM_PREFIX`, 23-series tool discovery, exact 23.1 admission, and both
`/usr/bin/clang` and `/usr/bin/clang-23.1` guest paths without a
`/usr/bin/clang-20` package entry.

This is source-contract coverage only. The macOS ARM64, Linux x86_64/ARM64,
Windows x64/ARM64 discovery matrix and the full x86_64/AArch64/RV32/RV64/WASM
compile/link matrix remain required runtime evidence under NFR-003 and NFR-007.

## Run the ad-hoc bootstrap smoke

Produce a current-source full Stage4 CLI and retain its adjacent provenance
sidecar. Admission requires `artifact_kind=pure-simple-full-cli`, the exact
candidate/source/producer/parent hashes, the Stage4 build log, and a hashed
essential-tools log whose completed gate is `stage4-essential-tools-smoke`.
Stage2, Stage3, `native_probe/simple`, and Rust's optional in-process LLVM lane
are diagnostic/provider artifacts only; none satisfies this production gate.

## Boot SimpleOS and exercise browser content

Run the canonical fullscreen evidence wrapper with the admitted nine-tool
provider and full Stage4 CLI. Production selection is
`SIMPLEOS_WM_NATIVE_BACKEND=llvm`; the build exports the canonical `SIMPLE_*`
tool paths, sets `SIMPLE_BOOTSTRAP=0`, retains
`SIMPLE_NATIVE_BUILD_LINKER_SCRIPT`, and uses
`build/simpleos_wm_fullscreen_evidence/native-cache/llvm`. Explicit
`SIMPLEOS_WM_NATIVE_BACKEND=cranelift` remains diagnostic-only and must never be
reported as LLVM 23.1 migration evidence. The wrapper stages the exact browser
ELF as `BROWSMF.SMF`, boots QEMU, launches it, and injects keyboard/pointer input.

## Validate retained rendering and input evidence

Require font, baseline, fullscreen, restored and browser frames; byte-identical
staging; browser provenance; and correlated keyboard, pointer and click events.
The admitted kernel record must agree with the selected `llvm` backend,
backend-scoped cache, `simple_bootstrap=0`, nine-tool identity, and Stage4
provenance hash; changing any field forces a rebuild instead of cache promotion.
Software presentation accepts only a strong `solid-material` or
`cpu-composited-material` receipt. Host-GPU presentation additionally accepts
`metal-device-composited-material`. Every receipt remains bound to a rendered
backend, a 64-lowercase-hex material digest, the expected theme and the exact
source manifest; any rejection marker or missing artifact fails the gate.

## Requirement traceability

| Requirement | Executable/source contract | Runtime evidence status |
|---|---|---|
| REQ-001, REQ-002, REQ-007 | Resolver and provider-builder assertions | Provider family admitted; stable 23.1 remains conditional on the same gate |
| REQ-003, REQ-008 | Browser builder and evidence-schema assertions | Client build/ELF evidence exists; complete focused final matrix remains required |
| REQ-004 | ELF, resolved `getpid`, staging and QEMU wrapper contract | Build/staging partial; guest launch plus correlated browser pixels incomplete |
| REQ-005 | Rust manifest, bootstrap rejection, isolation checker, and Cranelift CI assertions | Explicit isolation covered; Rust LLVM 23.1 support is not claimed |
| REQ-006 | Pure-Simple discovery and SimpleOS guest ownership assertions | Source contract covered; cross-host/runtime matrix incomplete |
| REQ-009 | Stage4 provenance and essential-tools contract assertions | Current full Stage4 plus essential-tools receipt incomplete |
| REQ-010 | Canonical fullscreen QEMU wrapper assertions | Live framebuffer/font/input/browser evidence incomplete |

## Acceptance-criterion traceability

| AC | Evidence owner | Current status |
|---|---|---|
| AC-1 | Local owned-code inventory | Recorded; source inventory evidence |
| AC-2 | Domain research and provider risk conclusions | Recorded; research evidence |
| AC-3 | Requirements, plans, executable spec, and this mirror | Partial until final trace/doc quality gate accepts unchanged artifacts |
| AC-4 | Provider resolver, pure-Simple discovery, guest paths | Partial; owned stale 18/20 references must be resolved or explicitly excluded |
| AC-5 | Exact-version resolver and actionable diagnostics | Source contract covered; final focused execution still required |
| AC-6 | Focused provider/browser/guest contracts | Partial; cross/freestanding runtime matrix is incomplete |
| AC-7 | Bootstrap logs, candidate provenance, essential-tools receipt | Incomplete: no admitted current full Stage4/essential-tools PASS |
| AC-8 | Browser ELF staging plus canonical QEMU evidence bundle | Incomplete: live browser/framebuffer/input evidence missing |
| AC-9 | Final unchanged-input compiler/core/lib/MCP, guards, SPipe and rendering gates | Incomplete |
| AC-10 | Operator/setup/CI/guide consistency scan | Incomplete while owned stale 18/20 instructions remain |
| AC-11 | Final verifier report | Incomplete; no `STATUS: PASS` |

## Nonfunctional traceability

| NFR | Source/evidence mapping | Current status |
|---|---|---|
| NFR-001 Reproducibility | rc2 tag/commit, tool hashes, candidate and output hashes | Partial until final Stage4/QEMU receipts bind unchanged inputs |
| NFR-002 Reliability | Missing/mixed/version/ELF/staging/capture fail-closed checks | Source contract covered; final live negative gates incomplete |
| NFR-003 Portability | Absolute prefix and platform-aware discovery | Partial: required macOS/Linux/Windows x64/ARM64 matrix incomplete |
| NFR-004 Maintainability | Shared resolver plus `SIMPLE_LLVM_PREFIX` ownership | Source contract covered; final duplication audit pending |
| NFR-005 Performance | Bounded executable/version probes | Source contract covered; representative timing evidence pending |
| NFR-006 Security | Signed provider identity and hash inventory | Provider evidence exists; final artifact chain incomplete |
| NFR-007 Compatibility | Target-specific compile/link gates | Incomplete: x86_64/AArch64/RV32/RV64/WASM matrix not complete |
| NFR-008 Evidence | Paths, versions, hashes, commands, targets, artifacts | Partial; Stage4 and live QEMU bundle missing |
| NFR-009 Iteration safety | Once-per-input rule and three-cycle cap | Active process constraint; not a substitute for missing evidence |

## Execution and limitations

Run the executable spec once with an admitted pure-Simple test runner, then
regenerate this mirror through SPipe docgen. A Rust seed or source-only review
cannot supply an executable PASS. The current edit was intentionally limited to
traceability and claim boundaries; it does not fabricate Stage4, external-host,
multi-architecture, or QEMU results.
