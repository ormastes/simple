# MinIO Share Skill

Generate a presigned download URL via `mc share download --json`.

## Prerequisites

- Configured alias (see `/minio setup`).
- Object exists; alias has `s3:GetObject` on the resource.

## Procedure

### Default (7-Day) Expiry

```bash
bin/itf minio share firmware-images/zynq/v1/fw.bin
# delegates to: mc --json share download <alias>/firmware-images/zynq/v1/fw.bin
```

`mc share download` defaults to `168h` (7 days) when `--expire` is omitted.

### Custom Expiry

Expiry is supplied in seconds; the adapter formats it as `mc`'s `##h##m##s` string:

```bash
bin/itf minio share firmware-images/zynq/v1/fw.bin 3600
# delegates to: mc --json share download --expire 1h <alias>/firmware-images/zynq/v1/fw.bin

bin/itf minio share firmware-images/zynq/v1/fw.bin 5400
# --expire 1h30m

bin/itf minio share firmware-images/zynq/v1/fw.bin 45
# --expire 45s
```

(Reference: `mc-share-download-2026` `--expire` accepts `##h##m##s`.)

### Limitations

- `mc share download` requires `--recursive` when the path points at a bucket or prefix; the adapter's single-object form does NOT pass `--recursive`. For prefix shares, drop to `mc` directly:
  ```bash
  mc --json share download --recursive --expire 1h <alias>/firmware-images/zynq/
  ```
- Maximum lifetime is enforced by the server (typically 7 days for SigV4 presigned URLs).

## Output

Each NDJSON line contains:
```json
{"status":"success","share":"https://minio.corp:9000/firmware-images/...?X-Amz-Signature=..."}
```

`mc_share_download` returns the `share` field as `presigned_url`.

## Error Handling

- HTTP 403 / `AccessDenied`: alias lacks `s3:GetObject`.
- HTTP 404 / `NoSuchKey`: object missing; run `/minio ls` first.
- Expiry out of range: server rejects presigns longer than 7 days for SigV4.

## Integration

- `/repo_and_pull_req push` includes presigned URLs to attached artifacts in PR descriptions.
- `/mail send` / `/mail notify` can embed the URL for review handoff.
