# Linux LLVM runtime link policy acceptance

Source: `test/01_unit/compiler/driver/xray_llvm_runtime_link_spec.spl`.

Status: authored acceptance manual; the full SSpec runner has not executed this revision. Historical native projection results cover earlier policy revisions only.

- Off and unrelated backend requests preserve their objects/options without compiler discovery.
- Canonical GNU Linux executable targets admit runtime preparation; unsupported targets and shared images refuse.
- Runtime object/flag/library planning preserves caller arrays and emits no Clang-only argument to a direct linker.
- Semantic-image flags preserve required SHA1 build identity and dead-section behavior, rejecting conflicting spellings.
- LLVM 18 architecture-suffixed archive names are resolved only for exact admitted targets. Relative, unresolved, cross-architecture, basic-logger and newline-bearing archive paths reject.

The production executor queries the same selected compiler with the exact target. Only an unresolved literal generic archive name triggers the architecture-specific query; failed or unexpected queries are errors. Actual archive existence remains mandatory. The observed read-only Clang 18 AArch64 query returned `/usr/lib/llvm-18/lib/clang/18/lib/linux/libclang_rt.xray-aarch64.a`; this verifies the toolchain lookup seam, not execution of the revised Simple materializer or public observer qualification.
