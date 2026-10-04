# macOS native facade verification

STATUS: FAIL — full item4/Phase 4 and five-host execution remain incomplete.

The explicit internal Unix route currently enters ELF handling even on macOS.
This lane connects the existing Mach-O image builder to native file/configuration
and request dispatch without changing hosted defaults or managed admission.
Acceptance must use actual object/archive/dylib fixtures and independently inspect
published commands and bytes, including failure preservation of a real sentinel.

The adapter is a prerequisite, not complete SDK support: text-based dylib stubs,
dyld-cache providers, remaining TLS/unwind/provider semantics, trusted internal
managed admission and actual x64/arm64 Darwin execution remain separate gates.
Windows/Linux/SimpleOS/FreeBSD native completion also remains open.

Simple compilation, executable acceptance, docgen, coverage, compiler/lib/MCP
and native performance qualification remain UNRUN without an admitted deployed
self-hosted runtime. Source and structural evidence must be recorded separately.
