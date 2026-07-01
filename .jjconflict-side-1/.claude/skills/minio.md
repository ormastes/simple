---
name: minio
description: MinIO / S3 object-storage CLI - `bin/itf minio` (ls/get/put/stat/presign/health) runs on the pure-Simple SigV4 adapter; raw `mc` is used only for the explicit prefix/recursive escape hatches.
---

# MinIO Skill - Dispatcher

MinIO/S3 client. The `bin/itf minio` subcommands (ls/get/put/stat/presign/health) are served by the pure-Simple SigV4 REST adapter (`adapter_minio.spl`) — **no `mc` binary is invoked** by the command. `adapter_minio_mc.spl` (mc-CLI delegation) exists but is **not wired into dispatch** — nothing imports it, so no command selects it at runtime. Raw `mc` is invoked only where a sub-doc explicitly says to "drop to `mc` directly" (recursive/prefix operations the SigV4 adapter's single-object forms don't cover).

## Usage

```
/minio <command> [args]
```

## Commands

| Command | `bin/itf minio` call | Description |
|---------|----------------------|-------------|
| setup | (installs `mc` for escape hatches) | Install `mc` + create alias — only needed for the recursive/prefix escape hatches, not the built-in subcommands |
| ls | `ls [bucket [--prefix P]]` | List buckets, or objects under a bucket/prefix |
| get | `get <bucket> <key> [--out PATH] [--range R]` | Fetch object body (or stream to `--out PATH`) |
| put | `put <bucket> <key> --file PATH [--content-type CT]` | Upload a file (text/JSON/XML up to 64 MiB; binary blocked) |
| share | `presign <bucket> <key> [--expires SECONDS]` | Generate a presigned GET URL (`/minio share` maps to `presign`; default 86400s, max 604800) |
| stat | `stat <bucket> <key>` | HEAD object (size/etag/last-modified) |

## Dispatch Logic

Argument: $ARGUMENTS

### Route

**setup:**
Read tools/claude-plugin/repo-and-pull-req/skills/minio/minio_setup.md and follow.

**ls [bucket [--prefix P]]:**
Read and follow tools/claude-plugin/repo-and-pull-req/skills/minio/minio_ls.md.

**get <bucket> <key> [--out PATH]:**
Read and follow tools/claude-plugin/repo-and-pull-req/skills/minio/minio_get.md.

**put <bucket> <key> --file PATH:**
Read and follow tools/claude-plugin/repo-and-pull-req/skills/minio/minio_put.md.

**share (→ `presign <bucket> <key> [--expires N]`):**
Read and follow tools/claude-plugin/repo-and-pull-req/skills/minio/minio_share.md.

**stat <path>:**
Run `bin/itf minio stat <bucket> <key>` (SigV4 HEAD via `adapter_minio.spl::_minio_stat` — returns size/etag/last-modified).

## Prerequisite Checks

- `bin/itf minio` requires a `[minio]` section in `~/.config/itf/auth.sdn` (url + region + access_key/secret_key) — the SigV4 adapter (`load_minio_config`) reads these. This is the only prerequisite for the built-in subcommands.
- `mc --version` / `mc alias list` - needed **only** for the explicit "drop to `mc`" escape hatches (recursive/prefix ls/get/put/share); the `bin/itf minio` subcommands do not call `mc`.

## Integration

| Skill | When Used |
|-------|-----------|
| /company_bug_report | Fetch firmware/dump artifacts referenced in Jira tickets |
| /repo_and_pull_req push | Attach build artifacts to PR via presigned URL |
| /bug_review fix | Pull crash dumps from MinIO before reproducing |
