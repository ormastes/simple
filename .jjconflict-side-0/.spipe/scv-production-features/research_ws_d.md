# Research: SCV Workstream D — PROD-005 (Network Remote Transport)

## 1. Current Filesystem Remote Architecture

### Source Files
- `src/lib/scv/public_remote.spl` (295 lines) — filesystem-backed public remote push/pull
- `src/lib/scv/pack.spl` (465 lines) — pack format, manifest, private-sync
- `src/lib/scv/integrity.spl` — fsck, object hash verification, repo health
- `src/lib/scv/fast_import.spl` — Git fast-import stream export/import
- `src/lib/scv/fast_import_format.spl` — bounded stream grammar, safe ref/path validation

### Filesystem Remote Protocol (public_remote.spl)
**Push** (`scv_public_push`):
1. Requires `public_ready` marker state
2. Calls `public-export` — runs `fsck`, writes content manifest, writes bounded Git fast-import stream, records `publish.sdn`
3. Writes artifact directory under `<remote-dir>/branches/<branch>/`
4. Updates `<remote-dir>/refs.sdn` — rewrites the branch row into one canonical ref, validates full table before persisting

**Pull** (`scv_public_pull`):
1. Reads branch row from `refs.sdn` (3-field: `branch|commit|artifact_path`)
2. Runs `scv_public_push_verify` — validates ref format, artifact path stays inside the selected branch dir (no redirect outside the remote root)
3. Imports bounded Git fast-import stream into local repo
4. Verifies manifest matches imported commit tree
5. Restores working copy via `scv_restore_op`

**Key invariant (security):** `public-push-verify` rejects refs whose artifact path redirects outside `<remote-dir>/branches/<branch>`. The network equivalent must enforce the same: a remote ref response must not redirect pack fetches to an attacker-controlled URL.

**Design doc quote (hook for PROD-005):**
> "`public-push` is the MVP shared-public transport … It is a filesystem remote only; network transport remains later work."
> — `doc/05_design/scv.md`, CLI Slice section

## 2. Pack Format (Transfer Units)

Packs are the wire-level unit for private-sync (`private-sync`) and will be the transport unit for network remote.

### Structure
- **Manifest** (`manifest.sdn`): text file with header `format: scv-pack-manifest-v1`, then rows `kind|id|size|path`
  - Supported kinds: `chunks`, `files`, `trees`, `syntax_nodes`, `operations`
  - Paths are object-relative: `chunks/<id>.blob`, `trees/<id>.sdn` (no absolute paths accepted)
  - Manifest body hashes to the pack id
- **Payload**: gzip-compressed archive; `pack-verify` decompresses, checks header, matches manifest entry counts, validates payload entry `kind/id/size/path`
- **Object verification**: every payload object re-hashes to its content-addressed id:
  - `chunks`: `scv_content_id_for_u8(raw)`
  - `files`, `trees`, `syntax_nodes`, `operations`: `scv_hash_text(kind, raw_text)`

### Relevant Functions (pack.spl)
| Function | Purpose |
|----------|---------|
| `scv_pack_manifest_has_entry` | Row lookup by kind/id/size/path |
| `scv_pack_payload_object_hash_ok` | Content-address re-verification |
| `scv_pack_manifest_entry_count` | Count non-header rows |
| `scv_pack_id_from_gzip_path` | Extract pack id from filename |

### Relevant Functions (integrity.spl)
`fsck` validates the entire object graph; `pack-verify [pack-id]` validates manifest header → manifest hash → payload header → entry parity → per-object hash. Both must pass before a network push completes.

## 3. Available Networking Primitives

Located under `src/lib/nogc_sync_mut/`:

| Module | Files | Notes |
|--------|-------|-------|
| `http_client/` | `connection.spl`, `request.spl`, `response.spl`, `ssl.spl`, `types.spl`, `utilities.spl`, `http.spl`, `tcp.spl`, `ffi.spl` | Full HTTP/HTTPS client; SSL support present |
| `net/` | `net.spl`, `tcp.spl`, `udp.spl`, `telnet.spl` | Raw TCP/UDP primitives |
| `oauth2.spl` | — | OAuth2 client credentials / token flow |
| `aws_sigv4.spl` | — | AWS SigV4 request signing (S3-compatible endpoints) |
| `http_server/` | — | For implementing a simple remote server endpoint |
| `dns/` | — | DNS resolution |

**Authentication options available:**
- `ssl.spl` — TLS for transport security
- `oauth2.spl` — token-based auth (suitable for shared public remotes with identity)
- `aws_sigv4.spl` — HMAC-SHA256 signed requests (suitable for S3/MinIO private backup)

## 4. Constraints and Risks

### A. Resumable Transfers
**Current pack format is NOT resumable as-is.** `private-sync` and `public-export` write a single gzip-compressed payload. Streaming the whole pack file via HTTP is not resumable.

**Natural resumability exists at object granularity.** The manifest lists each object separately with its content-addressed id. A per-object PUT protocol (upload each `kind/<id>.ext` individually, then finalize with manifest) is naturally re-entrant: any previously uploaded object can be detected via HEAD request and skipped. Interrupted transfers leave partial object sets; the receiver verifies completeness by comparing the manifest before accepting.

**Decision required (Architecture phase):** Choose between:
1. Whole-pack upload with HTTP range resume (simpler protocol, requires server-side range support)
2. Per-object upload (re-entrant, more round-trips, maps directly to pack manifest structure)

### B. Compare-and-Swap for Remote Refs
**Current FS impl** rewrites `refs.sdn` in place (validates first, then writes). No atomic CAS.

**Network equivalent needs CAS protocol.** Options:
- HTTP `If-Match: <etag>` / `If-None-Match` on the refs resource — standard HTTP conditional PUT
- Version token in `refs.sdn` incremented on each write; server rejects PUT if token mismatch
- CRDT-style append-only ref log (heavier, not aligned with current single-row-per-branch model)

**Recommended:** ETag-based conditional PUT for `refs.sdn`. Maps cleanly onto HTTP semantics and preserves the existing single-canonical-ref-per-branch invariant.

### C. Pack Integrity on Network
`pack-verify` already handles all needed checks. The network transport layer must:
1. Run `pack-verify` on the sender before transmitting
2. Run `pack-verify` again on the receiver after transfer completes
3. Reject the import if either fsck fails

This is already the pattern in `private-sync-import` (runs `fsck` after import).

### D. Public-Ready Gate
`public-push` requires the `public_ready` marker. Network transport must preserve this gate — a network push must call `public-export` (which enforces `public_ready`) before transmitting any artifact.

### E. Redirect/SSRF Risk
`public-push-verify` rejects artifact paths outside the remote branch dir. The network equivalent must validate that ref responses from the server only reference pack URLs within the authenticated remote origin — not third-party URLs (SSRF/confused-deputy risk).

## 5. Test Coverage

`test/02_integration/app/scv_public_remote_spec.spl` covers:
- Push/pull round-trip over filesystem remote
- Corrupt refs rejection
- Manifest mismatch rejection
- Duplicate branch ref rejection
- Artifact path redirect rejection

Network transport will need analogous specs with a local HTTP test server.

## 6. Implementation Approach Recommendations

1. **Define `ScvNetworkRemote` as a composition wrapper** around `http_client` (not inheriting from filesystem remote). Mirror the function signature shape of `scv_public_push`/`scv_public_pull` with a `remote_url: text` parameter instead of `remote_dir: text`.
2. **Use `aws_sigv4.spl` for private backup** (S3/MinIO target). Use `oauth2.spl` + TLS for shared public remotes with identity.
3. **Phase the resumable protocol:** start with whole-pack PUT (simpler), add per-object resume in a follow-up.
4. **CAS via HTTP conditional PUT** — ETag on `refs.sdn` resource. Server must return `412 Precondition Failed` on version conflict; client retries with fetch-then-push.
5. **Reuse `pack-verify` and `fsck` unchanged** — these are transport-agnostic. Network layer calls them before send and after receive.
6. **Local HTTP test server** using `http_server/` for integration specs — avoids external network dependency in CI.

## 7. Key File Paths

| Path | Role |
|------|------|
| `src/lib/scv/public_remote.spl` | Filesystem remote — template for network port |
| `src/lib/scv/pack.spl` | Pack format and manifest |
| `src/lib/scv/integrity.spl` | fsck and object verification |
| `src/lib/scv/fast_import.spl` | Git fast-import export/import |
| `src/lib/scv/fast_import_format.spl` | Stream grammar and safe validation |
| `src/lib/nogc_sync_mut/http_client/` | HTTP client primitives |
| `src/lib/nogc_sync_mut/http_client/ssl.spl` | TLS support |
| `src/lib/nogc_sync_mut/oauth2.spl` | OAuth2 auth |
| `src/lib/nogc_sync_mut/aws_sigv4.spl` | SigV4 for S3-compatible private backup |
| `src/lib/nogc_sync_mut/http_server/` | Local test server for integration specs |
| `doc/05_design/scv.md` | Design doc — network transport hook |
| `test/02_integration/app/scv_public_remote_spec.spl` | Existing remote test coverage |
