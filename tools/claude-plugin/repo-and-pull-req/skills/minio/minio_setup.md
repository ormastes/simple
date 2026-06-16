# MinIO Setup Skill

Setup for the ITF MinIO integration. The built-in `bin/itf minio` subcommands talk to S3 directly via the pure-Simple SigV4 adapter and need **only** a `[minio]` section in `~/.config/itf/auth.sdn` — no `mc` required. Installing `mc` (Steps 1–2) is optional and only enables the recursive/prefix escape hatches.

## Step 0 (required) — Configure credentials for the built-in path

`load_minio_config` reads a `[minio]` section from `~/.config/itf/auth.sdn`. The parser accepts either a flat `[minio]` header or an indented `minio:` header, and parses `key = value` pairs (use `=`, not `:`):

```
[minio]
url = https://minio.corp:9000
region = us-east-1
access_key = AKIAIOSFODNN7EXAMPLE
secret_key = wJalrXUtnFEMI/K7MDENG/bPxRfiCYEXAMPLEKEY
tls_skip_verify = false
```

Recognized keys: `url`, `region`, `access_key`, `secret_key`, `tls_skip_verify`. `check_minio_auth` requires `url`, `access_key`, and `secret_key` to be non-empty. (`tls_skip_verify = true` only logs a warning; runtime TLS-verify enforcement is a follow-up — not safe for production.)

Verify with:
```bash
bin/itf minio health           # probes /minio/health/live
bin/itf minio ls               # lists buckets
```

## Optional — Install `mc` (only for the escape hatches)

The recursive/prefix `mc --json ...` commands referenced in the other sub-docs need the MinIO Client on `PATH`. Skip this section unless you need them.

### Step 1 — Install mc

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

### Step 2 — Create an Alias

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

The `mc` alias lives in `mc`'s own config (`~/.mc/config.json`); the built-in `bin/itf minio` path does not read it.

## Verification Checklist

- [ ] `~/.config/itf/auth.sdn` has a `[minio]` (or `minio:`) section with `url`, `access_key`, `secret_key`
- [ ] `bin/itf minio health` reports alive
- [ ] `bin/itf minio ls` returns the bucket listing
- [ ] (escape hatches only) `mc --version` succeeds and `mc --json ls <alias>` works

## Error Handling

- `MinIO auth not configured. Set [minio] section in ~/.config/itf/auth.sdn`: Step 0 incomplete or used `:` instead of `=` for the values.
- `AccessDenied`: `access_key`/`secret_key` wrong or expired.
- `mc: command not found` (escape hatches): re-run Step 1 and check `PATH`.
