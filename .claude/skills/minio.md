---
name: minio
description: MinIO / S3 object-storage CLI - wraps the mc CLI for ls/get/put/share/stat/setup. Falls back to the pure-Simple SigV4 adapter when mc is not installed.
---

# MinIO Skill - Dispatcher

Shell-based MinIO/S3 client mirroring the mc CLI surface. Preferred backend: the official mc binary (delegates via adapter_minio_mc.spl); fallback when mc is absent: the pure-Simple SigV4 adapter (adapter_minio.spl).

## Usage

```
/minio <command> [args]
```

## Commands

| Command | Example | Description |
|---------|---------|-------------|
| setup | /minio setup | Install mc + create alias |
| ls <path> | /minio ls firmware-images/zynq/ | List bucket / prefix contents |
| get <remote> [local] | /minio get firmware-images/fw.bin ./fw.bin | Download an object |
| put <local> <remote> | /minio put ./fw.bin firmware-images/zynq/v2/ | Upload a file |
| share <path> [<expiry>] | /minio share firmware-images/fw.bin 1h | Generate presigned download URL |
| stat <path> | /minio stat firmware-images/fw.bin | Show object/bucket metadata |

## Dispatch Logic

Argument: $ARGUMENTS

### Route

**setup:**
Read tools/claude-plugin/repo-and-pull-req/skills/minio/minio_setup.md and follow.

**ls <path>:**
Read and follow tools/claude-plugin/repo-and-pull-req/skills/minio/minio_ls.md.

**get <remote> [local]:**
Read and follow tools/claude-plugin/repo-and-pull-req/skills/minio/minio_get.md.

**put <local> <remote>:**
Read and follow tools/claude-plugin/repo-and-pull-req/skills/minio/minio_put.md.

**share <path> [<expiry>]:**
Read and follow tools/claude-plugin/repo-and-pull-req/skills/minio/minio_share.md.

**stat <path>:**
Run `bin/itf minio stat <path>` (delegates to `mc --json stat <alias>/<path>`).

## Prerequisite Checks

- `mc --version` - preferred backend available
- `mc alias list` - at least one alias configured (run /minio setup if empty)
- If mc is absent: pure-Simple SigV4 backend kicks in via adapter_minio.spl; requires `[minio]` section in `~/.config/itf/config.sdn`

## Integration

| Skill | When Used |
|-------|-----------|
| /company_bug_report | Fetch firmware/dump artifacts referenced in Jira tickets |
| /repo_and_pull_req push | Attach build artifacts to PR via presigned URL |
| /bug_review fix | Pull crash dumps from MinIO before reproducing |
