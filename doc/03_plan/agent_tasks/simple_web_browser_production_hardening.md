# Simple Web Browser Production Hardening Agent Plan

## Parallel Agent Split

- Normal model artifact audit: inspect SPipe state, requirements, design, spec docs, reports, and tracking rows for Simple Web/browser hardening lanes. Output canonical lane names and missing artifacts only.
- Spark model implementation reconnaissance: inspect `src/app/ui.web`, `src/app/ui.browser`, browser/Web tests, and evidence wrappers. Output concrete hardening risks and one disjoint implementation slice only.

## Current Slice

Owns these files:

- `src/app/ui.web/session_token.spl`
- `src/app/ui.web/server.spl`
- `src/app/ui.web/tls_serve_loop.spl`
- `src/app/ui.web/ui_routes.spl`
- `test/01_unit/app/ui/web_auth_hardening_spec.spl`

Do not absorb unrelated GPU, crypto, compiler, or renderer-parity dirty files in this checkout.

## Remaining Work

- Add auth gates for sensitive `/api/*` browser/web introspection routes.
- Replace auth-path ad hoc JSON/query parsing with bounded structured helpers.
- Generate the mirrored scenario manual for the new hardening spec if it becomes a system-level SPipe spec.
- Run the full production GUI/Web renderer parity wrapper after the unresolved `jj` conflict is cleared.
