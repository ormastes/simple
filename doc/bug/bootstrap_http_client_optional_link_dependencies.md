# Client-only bootstrap inherits optional HTTP link requirements

Both LLVM and Cranelift Phase 2 refreshes from `f6026d340a59` compiled
1,189 modules with zero module failures, then failed linking the same 19
undefined HTTP/WebSocket runtime symbols. The HTTP re-export in the main I/O
facade made `http_sffi.spl` reachable; module-level retention also retained its
unrelated optional server and WebSocket wrappers. These legacy handle providers
have no implementation in the owned C or Rust runtime used by the candidates.

The repair moves supported client operations and their shared nominal types to
canonical client owners, forwards the existing compatibility facade to those
owners, and routes the main I/O facade directly to the supported client owner.
POST, form POST, PUT, PATCH, DELETE, and HEAD use the existing request provider;
URL encoding/decoding uses the existing pure Simple implementation. Optional
server/WebSocket declarations remain unchanged. No placeholder provider or
unresolved-symbol linker override is added.

The separate limitation remains: compiling a module that uses the optional
legacy handle APIs still requires real providers. Module-level retention can
also retain unused functions within that module. This change does not claim
those providers or function-level dead stripping are implemented.

The standalone native regression uses a local HTTP echo fixture and checks
actual method, content type, body, response/error propagation, UTF-8 URL
encoding/decoding, and malformed escapes. Native validation is pending; the
existing failed receipts, compiled objects, and caches remain preserved.
