# MinIO Get Skill

Download an object from MinIO via `bin/itf minio get` (pure-Simple SigV4 REST — `adapter_minio.spl`, no `mc`).

## Prerequisites

- `[minio]` section in `~/.config/itf/auth.sdn` (see `/minio setup`).
- For `--out PATH`, the destination path is writable.

Signature: `get <bucket> <key> [--out PATH] [--range R]`. Bucket and key are **separate** positional args.

## Procedure

### Stream Body to a File

```bash
bin/itf minio get firmware-images zynq/v1/fw.bin --out ./fw.bin
# → minio_download(cfg, "firmware-images", "zynq/v1/fw.bin", "./fw.bin", 3600); prints "wrote N bytes to ./fw.bin"
```

### Print Body to stdout

With no `--out`, the object body is written to stdout (`--json` wraps the raw response instead):

```bash
bin/itf minio get firmware-images zynq/v1/fw.bin
# → minio_get_object → prints result.body
```

### Byte Range

```bash
bin/itf minio get firmware-images zynq/v1/fw.bin --range bytes=0-1023 --out ./head.bin
# passes the HTTP Range header through
```

### Recursive (Prefix) Download

The built-in `get` is single-object only. For prefix downloads, run `mc` directly:

```bash
mc --json cp --recursive <alias>/firmware-images/zynq/ ./local/zynq/
```

(Reference: `mc-cp-2026` `--recursive`. Separate raw-`mc` escape hatch, not the built-in path.)

## Output

`--out PATH` writes the file and prints a `wrote N bytes` success line. Without `--out`, the raw body goes to stdout; `--json` prints `format_json_output(raw)` (the raw S3 response) instead.

## Error Handling

- `NoSuchKey`: path is wrong; verify with `/minio ls` first.
- `AccessDenied`: credentials lack `s3:GetObject`.
- Local `permission denied`: `--out` directory not writable.

## Integration

- Pair with `/minio stat` to verify size/etag before download.
- Used by `/company_bug_report` to fetch firmware artifacts referenced in Jira tickets.
