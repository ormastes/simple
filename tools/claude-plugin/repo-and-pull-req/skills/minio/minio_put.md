# MinIO Put Skill

Upload a local file to MinIO via `mc cp --json`.

## Prerequisites

- Configured alias (see `/minio setup`).
- Bucket exists; alias has `s3:PutObject` on the destination prefix.

## Procedure

### Upload Single File

```bash
bin/itf minio put ./fw.bin firmware-images/zynq/v2/fw.bin
# delegates to: mc --json cp ./fw.bin <alias>/firmware-images/zynq/v2/fw.bin
```

### Upload Into a Prefix

If the remote ends with `/`, `mc` preserves the source filename:

```bash
bin/itf minio put ./fw.bin firmware-images/zynq/v2/
# uploads as <alias>/firmware-images/zynq/v2/fw.bin
```

### Recursive Upload

`adapter_minio_mc.spl` covers single-file `put`. For directory upload, drop to `mc`:

```bash
mc --json cp --recursive ./build/artifacts/ <alias>/firmware-images/zynq/v2/
```

(Reference: `mc-cp-2026` `--recursive`.)

## Storage Class / Tags

Pass through `mc` flags:

```bash
mc --json cp --storage-class STANDARD --tags "build=ci" ./fw.bin <alias>/firmware-images/zynq/v2/fw.bin
```

## Error Handling

- HTTP 403 / `AccessDenied`: missing PutObject permission.
- HTTP 409 / `BucketAlreadyExists` / `OperationAborted`: retry after backoff.
- Local file missing: `mc` exits with code `1` and `<source>: stat: ...`.
- Large files (>5 GiB): mc auto-multiparts; ensure the alias's signature is `S3v4`.

## Integration

- Use after `bin/simple build` to publish artifacts.
- Pair with `/minio share` to hand off a presigned URL to a reviewer.
