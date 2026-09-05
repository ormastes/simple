<!-- codex-architecture -->
# LLVM 23.1 bootstrap binding — TLDR

Stage 4 needs one fail-closed 23.1 identity shared by Rust bindings, platform
discovery, and pure-Simple LLVM tools. The current Inkwell/llvm-sys 18 binding
cannot consume LLVM 23.1. Port or obtain a 231 binding first, then build the
host toolchain, update discovery/CI/tool probes, and invalidate every bootstrap
and SDK artifact. No LLVM 18/20 result is migration evidence.
