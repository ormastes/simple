# Confluence access boundaries

The canonical DevHub adapter owns request construction, transport interpretation and content parsing. `confluence_response_result` is the pure production boundary after the existing process facade returns curl stdout, stderr and exit code; offline tests supply those same values. HTTP failure bodies become redacted diagnostics. Success bodies are preserved.

Configuration owns credential scope and precedence. `resolve_auth_token` chooses the existing auth document path and delegates to `resolve_auth_token_from`; the latter accepts a fixture path without changing process-wide HOME. Named target selection changes the lookup key, never enabling a default-target fallback.

The JSON library owns decoding. CQL escaping remains local to its existing query builder. There is no new cache, retry loop or transport implementation. One request remains one curl process, and listing retains its existing caller-specified limit without automatic pagination.
