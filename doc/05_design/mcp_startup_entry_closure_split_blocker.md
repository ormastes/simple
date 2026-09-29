# MCP startup entry-closure split: native-loading blocker

## Decision

A behavior-preserving startup-only native closure cannot currently be implemented
by moving `main_dispatch` behind the existing MCP "lazy" registries.  Keep the
production entry unchanged until native code has a callable late-binding owner.

## Evidence

- `src/app/mcp/main.spl` calls `dispatch_tool` for `tools/call`; therefore the
  full dispatch is part of the executable behavior, not an optional feature.
- `src/app/mcp/main_dispatch.spl` statically imports every advertised handler
  category.  Its in-process dispatcher directly calls the debug, dialog, play,
  editor, assistant, node, context, and telemetry handlers.
- `src/lib/nogc_async_mut/mcp/lazy_registry_v2.spl` stores metadata only and
  explicitly cannot store callable function references.
- `src/lib/nogc_async_mut/mcp/category_loaders_v2.spl` only flips boolean flags;
  it does not load code.
- `src/app/mcp/bootstrap/main_lazy_v2.spl` uses lexical `use` statements inside
  dispatcher functions.  Native compilation resolves those imports ahead of
  time, so they remain in the entry closure; the source location does not make
  them dynamic.
- A focused diagnostic core-C build of `src/app/mcp/main.spl` retained 104
  unresolved runtime references.  Retained objects attributed 48 to
  `lib.nogc_sync_mut.simd`, 14 to `simd_crypto`, and 27 to `io.http_sffi`.
  These modules arrive through real advertised handler paths, so deleting the
  imports would delete behavior rather than minimize startup.

## Required boundary

Introduce one canonical native late-binding interface, owned below the MCP app:

1. Build handler categories as separately validated native modules with a
   versioned ABI: `mcp_handler_v1(name, id, body) -> text`.
2. Keep only handler metadata and initialize/tools-list response construction in
   the main executable.
3. On the first `tools/call`, resolve the category artifact through the loader,
   validate its ABI/version/digest, then cache its callable handle.
4. Fail closed with a JSON-RPC internal error when the artifact is absent,
   ambiguous, ABI-incompatible, or fails to load.  Never silently reduce the
   advertised tool table.
5. Package the executable and every category artifact as one immutable bundle;
   tools/list metadata and artifact digests must be generated from the same
   manifest.

The compiler entry-closure walker must treat only this validated loader call as
the boundary.  Ordinary `use`, including function-local `use`, must remain a
static dependency.

## Acceptance criteria for a future implementation

- Initialize and tools/list match the current production responses and tool
  inventory.
- A representative tool in every category produces the same response as the
  current static dispatcher.
- The startup executable's undefined-runtime census excludes HTTP/WS, SIMD,
  file-mmap, terminal, and process families unless startup code directly uses
  them.
- First-call loading is fail-closed and cached; repeated calls do not reopen or
  revalidate an unchanged artifact.
- Package and release checks prove all advertised categories are present before
  promotion.
