# MinIO List Skill

List buckets, prefixes, and objects via `mc ls --json`.

## Prerequisites

- `mc` installed and an alias configured (`/minio setup` if not).
- The target bucket exists and the alias's credentials grant `s3:ListBucket`.

## Procedure

### List Top-Level (Buckets)

```bash
bin/itf minio ls
# delegates to: mc --json ls <alias>
```

### List a Bucket / Prefix

```bash
bin/itf minio ls firmware-images/
# delegates to: mc --json ls <alias>/firmware-images/
```

### Recursive Listing

```bash
bin/itf minio ls firmware-images/zynq/ --recursive
# delegates to: mc --json ls --recursive <alias>/firmware-images/zynq/
```

If the path points at a bucket or prefix and `--recursive` is omitted, `mc` only lists the top level (per `mc-ls-2026`).

## JSON Output Shape

`mc --json` emits JSON Lines (one object per line; reference: mc-overview `--json` global flag). Each entry has:

```json
{"status":"success","type":"file","key":"zynq/v1/fw.bin","size":1048576,"lastModified":"2026-04-01T10:00:00Z","etag":"abc"}
```

`adapter_minio_mc.spl::mc_ls` parses these into `[McEntry]` and short-circuits on any line whose `status == "error"`.

## Error Handling

- Exit code `1` with `AccessDenied`: rotate creds via `mc alias set`.
- Exit code `2`: argv invalid - check the path syntax.
- Empty output for an existing bucket usually means the prefix has no keys.

## Integration

- Use before `/minio get` to confirm the object exists.
- Wrap in `bin/itf minio ls --output json | jq` for downstream pipelines.
