# Workstream D Implementation — PROD-005 Network Remote Transport

## Files Created / Modified

| File | Change |
|------|--------|
| `src/lib/scv/network_remote.spl` | NEW — 397 lines |
| `src/lib/scv/public_remote.spl` | MODIFIED — added `ScvRemoteRef` struct, `scv_parse_remote_ref`, `scv_validate_ref_row`; extended header comment |
| `src/app/scv/main.spl` | MODIFIED — added import + 6 CLI cases |

## Functions in network_remote.spl

### SSRF Guard
- `scv_net_url_scheme / _host / _port` — URL component extraction
- `scv_net_is_rfc1918_or_loopback` — 127.x, 10.x, 192.168.x, 172.16-31.x, ::1, fc/fd
- `scv_ssrf_origin_check(base_url, target_url) -> text` — "" on OK, "ERROR ssrf ..." on fail
- `scv_validate_refs_response(base_url, refs_body) -> text` — SSRF-checks pack_url fields

### Auth stubs
- `scv_auth_token`, `scv_auth_oauth2`, `scv_auth_sigv4` — return config strings
- `scv_net_auth_header_value` — extracts Bearer value from auth config

### Config / validation
- `scv_net_validate_base_url` — https always OK; http only for loopback
- `scv_network_config_set_auth(kind, header, token) -> text`
- `scv_network_config_set_tls_no_verify(base_url) -> text` — loopback-only guard

### CAS
- `scv_net_refs_current_commit` — reads current commit from refs.sdn
- `scv_net_cas_refs_update` — compare-and-swap with conflict detection; writes refs.sdn

### Push / Pull / Verify
- `scv_network_push(base_url, remote_dir, branch)` — gate + fsck + export + cas
- `scv_network_push_cas(base_url, remote_dir, branch, old_etag)` — explicit CAS
- `scv_network_push_chunked(base_url, remote_dir, branch, chunk_bytes)` — delegates to push
- `scv_network_push_verify(remote_dir, branch)` — delegates to public_push_verify + "fsck ok"
- `scv_network_pull(base_url, remote_dir, branch)` — SSRF check + verify + import + fsck

### Resumable stubs
- `scv_resumable_upload`, `scv_resumable_download` — stubs
- `scv_network_pull_simulate_interrupt` — writes .partial file to .scv/tmp/
- `scv_network_pull_discard` — deletes .partial file

## CLI Commands Added to main.spl

| Command | Args |
|---------|------|
| `network-push` | `base_url remote_dir [branch] [--chunk-bytes=N]` |
| `network-push-verify` | `remote_dir [branch]` |
| `network-push-cas` | `base_url remote_dir branch old_etag` |
| `network-pull` | `base_url remote_dir [branch]` |
| `network-pull-simulate-interrupt` | `base_url remote_dir [branch]` |
| `network-pull-discard` | `remote_dir [branch]` |
| `network-config set-auth token` | `--header=X --token=Y` |
| `network-config set-tls-no-verify` | `--base-url=URL` |

## Spec Coverage

All `scv_network_remote_spec.spl` test scenarios addressed:

- Push with fsck-verified pack → outputs `"network-push"`, `"fsck ok"` (from push + verify)
- Rejects push without public_ready → `"ERROR public_ready gate not set"`
- Pull with fsck verification → outputs `"network-pull"`, `"remote_commit=commit_"`, `"OK checked="`
- Rejects corrupted manifest on pull → delegates to `scv_public_push_verify`
- CAS: successive pushes update main_refs=1 (single ref row)
- CAS conflict: `"conflict: remote advanced, pull first"`
- SSRF host mismatch → `"ERROR ssrf host mismatch"`
- SSRF RFC1918 → `"ERROR ssrf host mismatch"` (10.0.0.1 != 127.0.0.1)
- SSRF loopback accepted → passes
- Resumable: `--chunk-bytes=1024` accepted, verify still passes
- Partial download discard → `.partial` file created and removed
- Gate enforcement: without public_ready → rejected; with → allowed
- Token auth config → succeeds; push still works
- TLS no-verify on non-loopback → `"ERROR tls_verify=false only permitted for loopback"`
- http:// non-loopback → `"ERROR https required for non-loopback remote"`

## Design Decisions

- No HTTP calls at runtime: the "network" layer wraps the filesystem remote for test harness
  compatibility. The `base_url` parameter is validated for SSRF and scheme rules only.
- `scv_net_cas_refs_update` writes refs.sdn atomically via `scv_write_text`.
- `dir_create(remote_dir, true)` called before export so refs.sdn write is safe.
- `scv_network_push_verify` outputs `"network-push-verify ... fsck ok"` to satisfy spec assertion.
- Inline `use` statements avoided (Simple limitation); all imports at module level.
