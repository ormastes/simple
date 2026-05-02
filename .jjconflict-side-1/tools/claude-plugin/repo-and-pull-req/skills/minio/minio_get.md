# MinIO Get Skill

Download an object from MinIO via `mc cp --json`.

## Prerequisites

- Configured alias (see `/minio setup`).
- Local destination path is writable; if it is a directory, the source filename is preserved.

## Procedure

### Download to Explicit Path

```bash
bin/itf minio get firmware-images/zynq/v1/fw.bin ./fw.bin
# delegates to: mc --json cp <alias>/firmware-images/zynq/v1/fw.bin ./fw.bin
```

### Download to Current Directory

```bash
bin/itf minio get firmware-images/zynq/v1/fw.bin
# delegates to: mc --json cp <alias>/firmware-images/zynq/v1/fw.bin .
```

### Recursive (Prefix) Download

`adapter_minio_mc.spl` exposes a single-object copy. For prefix downloads, run `mc` directly:

```bash
mc --json cp --recursive <alias>/firmware-images/zynq/ ./local/zynq/
```

(Reference: `mc-cp-2026` `--recursive` flag.)

## Output

`mc --json cp` streams progress lines (NDJSON) culminating in a `status: success` line. Stderr carries `mc` diagnostics.

## Error Handling

- HTTP 404 / `NoSuchKey`: path is wrong; verify with `/minio ls` first.
- HTTP 403 / `AccessDenied`: missing `s3:GetObject` permission.
- Local `permission denied`: destination directory not writable.
- Network drop: rerun the command; `mc` does not auto-resume single-object copies.

## Integration

- Pair with `/minio stat` to verify size/etag before download.
- Used by `/company_bug_report` to fetch firmware artifacts referenced in Jira tickets.
