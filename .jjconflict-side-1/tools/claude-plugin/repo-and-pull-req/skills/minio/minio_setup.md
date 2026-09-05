# MinIO Setup Skill

Interactive setup for the MinIO Client (`mc`) and ITF integration.

## Prerequisites Check

1. Check if `mc` is installed: `which mc`
2. If installed, check version: `mc --version`
3. List existing aliases: `mc --json alias list`

## Procedure

### Step 1 - Install mc

If `mc` is not on `PATH`, install per the MinIO AIStor Client quickstart:

Linux x86_64:
```bash
curl --progress-bar -L https://dl.min.io/aistor/mc/release/linux-amd64/mc \
    --create-dirs -o ~/.local/bin/mc
chmod +x ~/.local/bin/mc
~/.local/bin/mc --help
```

Linux ARM64: swap `linux-amd64` for `linux-arm64`.
macOS: swap `linux-amd64` for `darwin-arm64`.
Windows: download `windows-amd64/mc` and reference it as `mc.exe`.

Ensure `~/.local/bin` is on `PATH`. (Reference: mc-overview-2026 quickstart.)

### Step 2 - Create an Alias

```bash
mc alias set <alias_name> <url> <access_key> <secret_key>
```

Example:
```bash
mc alias set myaistor https://minio.corp:9000 AKIAIOSFODNN7EXAMPLE wJalrXUtnFEMI/K7MDENG/bPxRfiCYEXAMPLEKEY
```

Constraints (per `mc-alias-set-2026`):
- ALIAS: ASCII letters/digits/`-`/`_`, first char a letter, case-sensitive.
- SECRETKEY: at least 8 characters.
- Default signature: `S3v4` (use `--api S3v2` only for legacy services).

### Step 3 - Persist Alias for ITF

Save the alias name to `~/.config/itf/auth.sdn` so `cmd_minio.spl` can pick it up. The file format mirrors the existing `confluence:` / `jira:` sections (yaml-style key-value):

```
minio:
    alias_name: "myaistor"
```

(Secret credentials live inside `mc`'s own config at `~/.mc/config.json` and are NOT mirrored into `auth.sdn`.)

### Step 4 - Verify Access

```bash
mc --json alias list myaistor       # confirm registration
mc --json ls myaistor               # list buckets
mc admin info myaistor              # cluster info (admin creds only)
```

For health probing without `mc`:
```bash
curl -s -o /dev/null -w "%{http_code}\n" https://minio.corp:9000/minio/health/ready
# expect 200
```

## Verification Checklist

- [ ] `mc --version` succeeds
- [ ] `mc --json alias list` shows the new alias
- [ ] `mc --json ls <alias>` returns at least the bucket listing
- [ ] `~/.config/itf/auth.sdn` contains a `minio:` section with `alias_name`

## Error Handling

- `mc: command not found`: re-run Step 1 and check `PATH`.
- HTTP 403 / `AccessDenied`: secret key wrong or expired. Re-run `mc alias set`.
- HTTP 503 / `ServiceUnavailable`: server overloaded; back off and retry.
- TLS errors: add `--insecure` (mc) only for self-signed dev hosts.
