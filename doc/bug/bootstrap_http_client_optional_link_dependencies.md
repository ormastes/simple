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

## 2026-10-21 stateless application dependency follow-up

At release revision `20128a8a9e6`, seven stateless application transport
imports still reached the broad `http_sffi` owner: DevHub API/MinIO, Caret's
Claude/OpenAI/compatible/multimodal providers, and the LLM runtime transport.
They now import their existing supported functions and types directly from
`http_client_core`. No function body, request policy, nominal type, provider,
or configured importer family changes.

The HTTP source audits also followed the obsolete single-owner layout after
the earlier client-core isolation. They now check the three actual owners
individually: `http_sffi` has 23 declarations/17 scoped calls,
`http_client_core` has 3/11, and `http_get_core` has 1/1. The total remains
27 declarations and 29 scoped calls. Lossless v2 checks follow its actual
`http_client_core` owner. Both HTTP audits pass with this layout; no inventory
ceiling or allowlist was relaxed.

This is a dependency repair within the narrowed bootstrap-through-Phase3
scope. It does not establish complete HTTP or Windows transport availability.
The configured UI client still imports `http_sffi`; that owner declares a
default-header setter with no native implementation at this revision. A
separate native slot/header repair and UI-owner extraction remain unlanded:
their CI failed `local-rt-dual-implementation` for a new C-only setter and
private helpers. The guard currently compares owned C and Rust definitions,
despite describing the desired C/Simple/alias architecture. No policy change
or cosmetic twin was added to bypass that failure.

Windows native request paths also still return their explicit unavailable
error. Native live HTTP, complete product builds, and Phase3 qualification
remain separate verification work. The existing 15-check stateless native
echo probe remains applicable once a usable self-hosted producer and transport
are available; its existence is not execution evidence.
