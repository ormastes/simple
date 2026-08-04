<!-- codex-design -->
# Clang 23.1 and Browser Demo Architecture

## Decision

Treat LLVM/Clang 23.1 as one admitted toolchain capsule rather than a collection
of independently discovered executables.  The present reproducible provider is
the signed `llvmorg-23.1.0-rc2` source release; the admission predicate is parsed
major `23`, minor `1`, so a later stable 23.1 provider can replace it without a
source change.

## Capsules and ownership

1. **Host provider capsule** resolves an explicit prefix first, then bounded
   platform names. It returns canonical absolute paths for `clang`, `ld.lld`,
   `llc`, `opt`, `llvm-ar`, `llvm-nm`, `llvm-objdump`, `llvm-objcopy`, and
   `llvm-config`, plus parsed versions. A missing or mixed family is an error.
2. **Pure-Simple compiler capsule** owns compiler/interpreter/runtime discovery
   and exposes the same preference and diagnostic contract without shelling out
   repeatedly in hot compilation paths. It consumes only that provider through `SIMPLE_LLVM_PREFIX` and the
   matching `SIMPLE_*` overrides. A provenance-verified full Stage 4 CLI is the
   production provider; Stage 2/3 and ad-hoc native probes are bootstrap
   evidence only.
3. **Rust bootstrap capsule** owns the LLVM C-API binding.  An LLVM-18-only
   `inkwell` feature cannot masquerade as 23.1; unsupported upstream bindings
   are a release blocker or the LLVM feature must be explicitly unavailable.
4. **SimpleOS port capsule** owns guest paths, manifests, package metadata and
   launch aliases.  `/usr/bin/clang-23.1` is canonical and `/usr/bin/clang` is
   its stable alias.
5. **Browser evidence capsule** compiles the browser source and isolated libc
   with the admitted Clang, links with the admitted LLD, stages the exact ELF,
   and delegates rendering/input proof to the existing fullscreen QEMU gate.

The capsules communicate through explicit paths and retained evidence, never by
rescanning the filesystem or silently falling back to LLVM 18/20/22.

## Data and control flow

`LLVM_23_1_PREFIX` + `SIMPLE_LLVM_PREFIX` (with exact tool overrides) -> resolver -> version and
coherence validator -> compiler/sysroot/libc/linker -> ELF/hash -> disk staging
and byte comparison -> SimpleOS guest execution -> QMP framebuffer and input
correlation report.

## Failure model

Missing tools, unparsable versions, major/minor mismatch, mixed tool families,
unsupported target compilation, unresolved runtime symbols, changed source,
staging mismatch, absent guest execution, or incomplete frames/events all fail
closed with the rejected path and remediation.  The provider is never fetched
implicitly by a production compile path.

## Compatibility boundary

The required target matrix is X86, AArch64, RISC-V, WebAssembly and the custom
freestanding SimpleOS triples.  Each is proven by a focused compile or backend
target check.  LLVM IR/bitcode is not exchanged backward with LLVM 18 tools.
Object and archive boundaries remain the portability boundary.

## Performance and security

Resolution uses a fixed candidate list and at most one `--version` probe per
candidate per process.  No recursive search/download belongs in compilation or
request hot paths.  Provider construction is an operator action from a signed
tag; evidence retains tag/commit, binary versions and SHA-256 identities.
