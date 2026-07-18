# Spec: SCV Workstream D — PROD-005 Network Remote Transport

**Status:** Draft  
**Spec file:** `test/02_integration/app/scv_network_remote_spec.spl`  
**Architecture:** `.spipe/scv-production-features/arch_ws_d.md`  
**AC covered:** AC-5

## Test Groups and Coverage

### 1. Network Push with fsck-verified pack (3 tests)
- Happy-path push to loopback HTTP remote; verifies manifest exists and fsck passes
- Rejects push when `public_ready` gate has not been set (exit 1 + ERROR public_ready gate not set)
- Rejects push when local pack file is corrupted (fsck failure → exit 1)

### 2. Network Pull with pack verification (2 tests)
- Happy-path pull from loopback remote; compares file content, verifies fsck OK and remote_commit
- Rejects pull when remote manifest hash is corrupted (`sha256_bad` injection → exit 1)

### 3. CAS Ref Update (2 tests)
- Successful two-push sequence; refs.sdn shows one `main` row with updated commit id
- Conflict scenario: concurrent advance detected → `conflict: remote advanced, pull first` (exit 1)

### 4. SSRF Origin Validation (3 tests)
- Rejects refs response with pack_url pointing to different host (`http://internal-corp/`)
- Rejects refs response with pack_url resolving to RFC1918 address (`http://10.0.0.1/`)
- Accepts pack_url within same loopback origin (127.0.0.1) — ssrf_ok=1

### 5. Interrupted Transfer Resume / Discard (2 tests)
- Chunked upload (`--chunk-bytes=1024`) completes and verifies cleanly
- Simulated interrupted download: partial files cleaned up by `network-pull-discard` (after_discard=0)

### 6. `public_ready` Gate Enforcement (2 tests)
- Push after snapshot+test-gate but without `public-ready` → ERROR public_ready gate not set
- Push after all gates including `public-ready` → succeeds (push_allowed=1)

### 7. Auth Method Configuration (3 tests)
- Token auth (`--header=Authorization --token=...`) configured; push succeeds
- `tls_verify=false` on non-loopback https URL → ERROR tls_verify=false only permitted for loopback
- `http://` base_url for non-loopback host → ERROR https required for non-loopback remote

## CLI Subcommands Exercised
| Subcommand | Purpose |
|---|---|
| `network-push <base_url> <remote_dir> <branch>` | Push with public_ready + fsck gate |
| `network-push-verify <remote_dir> <branch>` | Verify pushed artifact integrity |
| `network-push-cas <base_url> <remote_dir> <branch> <etag>` | CAS update only (conflict testing) |
| `network-pull <base_url> <remote_dir> <branch>` | Pull + pack verify + fast-import |
| `network-pull-simulate-interrupt ...` | Test-only interrupt injection |
| `network-pull-discard <remote_dir> <branch>` | Discard partial download |
| `network-config set-auth token ...` | Configure Token auth |
| `network-config set-tls-no-verify ...` | Set tls_verify=false (loopback only) |

## Notes
- All tests use loopback (`http://127.0.0.1`) + `tls_verify=false` per arch §4 CI/test row
- SSRF rejection tests use crafted `refs.sdn` files (no live server needed)
- CAS conflict test manually writes a raced-ahead `refs.sdn` then calls `network-push-cas` with the stale etag
- Partial-download discard test relies on `network-pull-simulate-interrupt` (test-only subcommand)
