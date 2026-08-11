# Architecture: SCV Workstream D — PROD-005 (Network Remote Transport)

## 1. Module List

| File | Status | Responsibility |
|------|--------|----------------|
| `src/lib/scv/network_remote.spl` | **NEW** | HTTP push/pull, auth, SSRF guard, resumable transfer |
| `src/lib/scv/public_remote.spl` | **MODIFY** | Extract shared `ScvRemoteRef` and `ScvPublicReadyGuard` structs; add `ScvRemoteTransport` trait (composition point) |

No other scv files modified. `pack.spl`, `integrity.spl`, `fast_import.spl` used read-only.

---

## 2. Key Interfaces

### 2a. Remote Configuration

```
# Auth variants — no inheritance, tagged union via enum
enum ScvRemoteAuth {
    Token { header_name: text, token: text },
    OAuth2 { token_url: text, client_id: text, client_secret: text },
    SigV4  { access_key: text, secret_key: text, region: text, service: text },
    None,
}

struct ScvNetworkRemoteConfig {
    base_url: text,       # https://host/repo — SSRF-validated on construction
    auth: ScvRemoteAuth,
    tls_verify: bool,     # must default true; test-only override
    chunk_bytes: i64,     # 0 = whole-pack, >0 = per-chunk upload size
}

fn scv_network_remote_config(base_url: text, auth: ScvRemoteAuth) -> Result<ScvNetworkRemoteConfig, text>
# Validates: scheme must be https (or http only when host == 127.0.0.1/::1),
# host must not resolve to RFC1918/loopback unless tls_verify=false is explicit.
```

### 2b. Network Push

```
fn scv_network_push(
    cfg: ScvNetworkRemoteConfig,
    repo_dir: text,
    branch: text,
) -> Result<text, text>
# Steps (see §3 data flow):
# 1. public_ready gate
# 2. fsck + pack-verify (reuse integrity.spl)
# 3. GET refs etag
# 4. upload pack (whole or chunked)
# 5. CAS PUT refs with If-Match etag
# Returns new commit id on success, error text on failure/conflict.
```

### 2c. Network Pull

```
fn scv_network_pull(
    cfg: ScvNetworkRemoteConfig,
    repo_dir: text,
    branch: text,
) -> Result<text, text>
# 1. GET refs.sdn — validate pack_url stays within cfg.base_url origin
# 2. scv_ssrf_origin_check(cfg.base_url, pack_url)
# 3. download pack (whole or chunked)
# 4. pack-verify locally
# 5. fast-import + manifest verify
# 6. scv_restore_op
# Returns commit id on success.
```

### 2d. Resumable Transfer

```
fn scv_network_upload_pack(
    cfg: ScvNetworkRemoteConfig,
    pack_path: text,
    pack_id: text,
) -> Result<(), text>
# If cfg.chunk_bytes == 0: single PUT /packs/<pack_id>.gz
# If cfg.chunk_bytes > 0:
#   - For each manifest entry: HEAD /objects/<kind>/<id> — skip if 200
#   - PUT /objects/<kind>/<id> for missing objects
#   - POST /packs/<pack_id>/finalize with manifest

fn scv_network_download_pack(
    cfg: ScvNetworkRemoteConfig,
    pack_url: text,       # SSRF-checked before call
    dest_path: text,
) -> Result<(), text>
# GET pack_url, stream to dest_path
# On partial response (206): resume with Range header from current file size
```

### 2e. SSRF Guard and Origin Validation

```
fn scv_ssrf_origin_check(base_url: text, target_url: text) -> Result<(), text>
# Rejects if:
# - target_url scheme != base_url scheme
# - target_url host != base_url host (exact match, no subdomain wildcard)
# - target_url port != base_url port (when explicit)
# - target_url host resolves to RFC1918 / loopback (127.0.0.0/8, 10/8, 172.16/12, 192.168/16, ::1, fc00::/7)
# Mirrors the artifact-path containment check in scv_public_push_verify.

fn scv_validate_refs_response(base_url: text, refs_body: text) -> Result<ScvRemoteRef, text>
# Parses refs.sdn branch row; calls scv_ssrf_origin_check on pack_url field.
```

---

## 3. Data Flow

### Push
```
local repo
  └─ public_ready gate ──► scv_public_export (fsck + manifest + fast-import stream)
       └─ pack-verify ──► scv_network_upload_pack
            └─ whole PUT or per-object PUT sequence
                 └─ GET /refs etag
                      └─ PUT /refs If-Match:<etag> (CAS)
                           ├─ 200 OK ──► done, return commit_id
                           └─ 412 ──► retry: re-fetch refs, re-check diverge, re-PUT (max 3)
```

### Pull
```
GET /refs.sdn ──► scv_validate_refs_response (origin check)
  └─ scv_network_download_pack(pack_url) ──► local tmp path
       └─ pack-verify ──► scv_fast_import (bounded stream)
            └─ manifest verify ──► scv_restore_op ──► done
```

---

## 4. Auth Model

| Target | Auth Variant | Module Used |
|--------|-------------|-------------|
| Shared public remote (HTTPS) | `Token` (Bearer) | `http_client/request.spl` Authorization header |
| Identity-gated public remote | `OAuth2` | `oauth2.spl` client-credentials flow; token cached in memory |
| S3 / MinIO private backup | `SigV4` | `aws_sigv4.spl` per-request HMAC-SHA256 signing |
| CI / test | `None` (http only when loopback) | `http_client/` directly |

TLS enforced by default via `ssl.spl`. `tls_verify=false` only permitted when host resolves to loopback (test harness).

---

## 5. File Ownership (Disjoint)

| File | Owner | Change type |
|------|-------|-------------|
| `src/lib/scv/network_remote.spl` | Workstream D | Create |
| `src/lib/scv/public_remote.spl` | Workstream D | Modify — extract `ScvRemoteRef` struct + `scv_validate_ref_row` fn; no behavioral change to existing push/pull |
| `src/lib/scv/pack.spl` | Read-only | No change |
| `src/lib/scv/integrity.spl` | Read-only | No change |
| `src/lib/scv/fast_import.spl` | Read-only | No change |
| `src/lib/nogc_sync_mut/oauth2.spl` | Read-only | No change |
| `src/lib/nogc_sync_mut/aws_sigv4.spl` | Read-only | No change |

---

## 6. Open Decisions

1. **Server-side protocol** — client design is complete; server stub (`http_server/`-based) is out of scope for this workstream but needed for integration specs.
2. **Chunk size default** — recommend 8 MiB (matches typical S3 multipart minimum); whole-pack mode is the v1 default.
3. **CAS retry cap** — 3 retries before returning `Err("conflict: remote advanced, pull first")`.
