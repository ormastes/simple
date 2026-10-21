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

## 2026-10-21 application closure follow-up

At `380200890ff`, DevHub API/MinIO, Caret provider transports, and the
LLM runtime transport still imported supported client calls through
`http_sffi`. The UI access CLI also imported supported configured-client
handles through that broad owner. Those dependencies retained the optional
server/WebSocket wrappers despite the earlier main-I/O-facade isolation.

The follow-up routes the seven stateless application imports directly to
`http_client_core`. It moves the existing configured-client declarations,
nominal `HttpClient` type, and five unchanged wrappers to
`http_client_handles`, re-exporting them through the compatibility facade.
The UI access CLI imports that supported owner directly. The importer family
remains explicitly `nogc_sync_mut`; no selection fallback or provider is added.

The HTTP SFFI audits previously assumed a single declaration owner. Their
inventory now checks all four physical owners individually: 27 declarations
and 29 raw calls in total, with lexical FFI authority unchanged. Lossless v2
signature checks follow its canonical `http_client_core` owner.

Validation in the isolated Windows worktree:

- `bash scripts/audit/http-sffi-contracts.shs`: PASS.
- `bash scripts/audit/http-sffi-call-authority.shs`: PASS.
- `bash scripts/audit/direct-env-runtime-guard.shs --working`: PASS.
- `bash scripts/audit/direct-env-runtime-guard.shs --staged`: PASS (empty stage).

These are source/contract checks, not native compilation or execution.
`test/04_smoke/http_client_handles_native_probe.spl` adds nine real configured
client checks against a local echo fixture: allocation, timeout validation,
default headers and POST payload, destruction, generation separation, and
stale/invalid handles. Native execution remains pending a usable self-hosted
producer; the tracked `bin/simple.exe` is a Rust seed and was not used.
The existing 15-check stateless client native probe also remains applicable.
Build both probes with the candidate's `native-build --source src/compiler
--source src/app --source src/lib --entry-closure --entry <probe> --output
<isolated-output>`, then execute with `--url=http://127.0.0.1:PORT/` against a
fixture returning `METHOD|Content-Type|body` (HEAD has an empty response body).
Neither probe proves complete DevHub/Caret/MCP product build admission.
