# MinIO List Skill

List buckets, or objects under a bucket/prefix, via `bin/itf minio ls` (pure-Simple SigV4 REST — `adapter_minio.spl`, no `mc`).

## Prerequisites

- `[minio]` section in `~/.config/itf/auth.sdn` (url + region + access_key/secret_key); see `/minio setup`.
- The target bucket exists and the credentials grant `s3:ListBucket`.

## Procedure

### List Top-Level (Buckets)

```bash
bin/itf minio ls
# → minio_list_buckets (SigV4 GET /) → table [NAME, CREATED]
```

### List a Bucket / Prefix

The bucket is a positional arg; the prefix is the `--prefix` flag (not a path suffix):

```bash
bin/itf minio ls firmware-images --prefix zynq/v1/
# → minio_list_objects(cfg, "firmware-images", "zynq/v1/") → table [KEY, SIZE, MODIFIED]
```

### Recursive Listing

The built-in `ls` has no `--recursive` flag; `--prefix` already returns all keys under the prefix. For `mc`-style recursive/delimiter behavior, drop to `mc` directly:

```bash
mc --json ls --recursive <alias>/firmware-images/zynq/
```

(Reference: `mc-ls-2026` `--recursive` flag. This is a separate raw-`mc` escape hatch, not the built-in path.)

## JSON Output Shape

Default output is a formatted table. With `--json`, the command prints the raw S3 REST list response via `format_json_output(raw)` — it does **not** emit `mc` JSON-Lines, and nothing in the built-in path goes through `adapter_minio_mc.spl`.

```bash
bin/itf minio ls firmware-images --prefix zynq/ --json
```

## Error Handling

- `AccessDenied`: credentials lack `s3:ListBucket` — fix the `[minio]` keys in `auth.sdn`.
- Auth not configured: `MinIO auth not configured. Set [minio] section in ~/.config/itf/auth.sdn`.
- Empty output for an existing bucket usually means the prefix has no keys.

## Integration

- Use before `/minio get` to confirm the object exists.
- Pipe `bin/itf minio ls ... --json | jq` for downstream pipelines.
