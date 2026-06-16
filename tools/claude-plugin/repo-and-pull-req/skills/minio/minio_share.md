# MinIO Share Skill

Generate a presigned download URL. The `/minio share` verb maps to `bin/itf minio presign` (pure-Simple SigV4 — `adapter_minio.spl::minio_presign_get`, no `mc`).

## Prerequisites

- `[minio]` section in `~/.config/itf/auth.sdn` (see `/minio setup`).
- Object exists; credentials have `s3:GetObject` on the resource.

Signature: `presign <bucket> <key> [--expires SECONDS]`. Bucket and key are **separate** positional args.

## Procedure

### Default (1-Day) Expiry

```bash
bin/itf minio presign firmware-images zynq/v1/fw.bin
# → minio_presign_get(cfg, "firmware-images", "zynq/v1/fw.bin", 86400); prints the URL
```

The built-in default is `--expires 86400` (1 day) when the flag is omitted.

### Custom Expiry

Expiry is supplied in seconds via `--expires`:

```bash
bin/itf minio presign firmware-images zynq/v1/fw.bin --expires 3600     # 1 hour
bin/itf minio presign firmware-images zynq/v1/fw.bin --expires 5400     # 90 minutes
```

### Limitations

- The built-in `presign` is single-object only. For prefix/recursive shares, drop to `mc` directly:
  ```bash
  mc --json share download --recursive --expire 1h <alias>/firmware-images/zynq/
  ```
  (Separate raw-`mc` escape hatch, not the built-in path.)
- Maximum lifetime is enforced by the server (typically 7 days for SigV4 presigned URLs); the `presign` help caps `--expires` at 604800.

## Output

`presign` prints the presigned URL to stdout (one line) — not NDJSON. The `mc` JSON-Lines `share` shape applies only to the raw-`mc` escape hatch above.

## Error Handling

- `AccessDenied`: credentials lack `s3:GetObject`.
- `NoSuchKey`: object missing; run `/minio ls` first.
- Expiry out of range: server rejects presigns longer than 7 days for SigV4.

## Integration

- `/repo_and_pull_req push` includes presigned URLs to attached artifacts in PR descriptions.
- `/mail send` / `/mail notify` can embed the URL for review handoff.
