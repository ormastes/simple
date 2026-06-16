# MinIO Put Skill

Upload a local file to MinIO via `bin/itf minio put` (pure-Simple SigV4 REST — `adapter_minio.spl`, no `mc`).

## Prerequisites

- `[minio]` section in `~/.config/itf/auth.sdn` (see `/minio setup`).
- Bucket exists; credentials have `s3:PutObject` on the destination key.

Signature: `put <bucket> <key> --file PATH [--content-type CT]`. Bucket and key are **separate** positional args; the body comes from `--file`.

## Procedure

### Upload Single File

```bash
bin/itf minio put firmware-images zynq/v2/fw.bin --file ./fw.bin
# → reads ./fw.bin; text/JSON/XML up to 64 MiB → minio_put_text; prints "uploaded firmware-images/zynq/v2/fw.bin (N bytes, text path)"
```

### Content Type

```bash
bin/itf minio put firmware-images zynq/v2/meta.json --file ./meta.json --content-type application/json
```

### Binary Bodies

The built-in `put` currently handles **text bodies** (UTF-8, up to 64 MiB). Binary files fall through to `minio_put_object`, which returns a clear "needs raw-bytes SFFI" error (issue #10 follow-up). For binary/recursive uploads, drop to `mc` directly:

```bash
mc --json cp --recursive ./build/artifacts/ <alias>/firmware-images/zynq/v2/
```

(Reference: `mc-cp-2026` `--recursive`. Separate raw-`mc` escape hatch, not the built-in path.)

## Error Handling

- `--file PATH is required`: the `--file` flag was omitted.
- `AccessDenied`: credentials lack `s3:PutObject`.
- Binary body: surfaces the "needs raw-bytes SFFI" error — use the `mc` escape hatch above.

## Integration

- Use after `bin/simple build` to publish text/JSON artifacts.
- Pair with `/minio share` to hand off a presigned URL to a reviewer.
