# Adapter Minio Mc Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Adapter Minio Mc Specification

## Scenarios

### MinIO mc adapter

#### argv builders

#### alias set produces positional ALIAS URL ACCESSKEY SECRETKEY

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val argv = _argv_alias_set("myaistor", "https://x:9000", "AKIA-", "SECRET")
expect(argv.len()).to_equal(7)
expect(argv[0]).to_equal("--json")
expect(argv[1]).to_equal("alias")
expect(argv[2]).to_equal("set")
expect(argv[3]).to_equal("myaistor")
expect(argv[4]).to_equal("https://x:9000")
expect(argv[5]).to_equal("AKIA-")
expect(argv[6]).to_equal("SECRET")
```

</details>

#### alias remove takes a single alias arg

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val argv = _argv_alias_remove("myaistor")
expect(argv).to_equal(["--json", "alias", "remove", "myaistor"])
```

</details>

#### alias list takes no extra args

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val argv = _argv_alias_list()
expect(argv).to_equal(["--json", "alias", "list"])
```

</details>

#### ls without recursive omits -r

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val argv = _argv_ls("a", "bucket/prefix/", false)
expect(argv).to_equal(["--json", "ls", "a/bucket/prefix/"])
```

</details>

#### ls with recursive emits --recursive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val argv = _argv_ls("a", "bucket/", true)
expect(argv).to_equal(["--json", "ls", "--recursive", "a/bucket/"])
```

</details>

#### stat qualifies bucket-relative path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val argv = _argv_stat("a", "bucket/key.bin")
expect(argv).to_equal(["--json", "stat", "a/bucket/key.bin"])
```

</details>

#### cp download orders ALIAS/remote then LOCAL

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val argv = _argv_cp_get("a", "bucket/k.bin", "/tmp/out")
expect(argv).to_equal(["--json", "cp", "a/bucket/k.bin", "/tmp/out"])
```

</details>

#### cp upload orders LOCAL then ALIAS/remote

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val argv = _argv_cp_put("a", "/tmp/in", "bucket/k.bin")
expect(argv).to_equal(["--json", "cp", "/tmp/in", "a/bucket/k.bin"])
```

</details>

#### share download includes --expire=<duration>

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val argv = _argv_share_download("a", "bucket/k", 3600)
expect(argv).to_equal(["--json", "share", "download", "--expire", "1h", "a/bucket/k"])
```

</details>

#### admin info passes alias as TARGET

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val argv = _argv_admin_info("myaistor")
expect(argv).to_equal(["--json", "admin", "info", "myaistor"])
```

</details>

#### health curl probes /minio/health/ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val argv = _argv_health("https://minio.corp:9000")
expect(argv[0]).to_equal("-s")
expect(argv[5]).to_equal("https://minio.corp:9000/minio/health/ready")
```

</details>

#### health curl strips trailing slash from url

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val argv = _argv_health("https://x/")
expect(argv[5]).to_equal("https://x/minio/health/ready")
```

</details>

#### _qualify_path

#### concatenates alias and bucket path

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_qualify_path("a", "bucket/key")).to_equal("a/bucket/key")
```

</details>

#### strips a leading slash from path

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_qualify_path("a", "/bucket/key")).to_equal("a/bucket/key")
```

</details>

#### _format_expire

#### 1 hour -> 1h

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_format_expire(3600)).to_equal("1h")
```

</details>

#### 1 hour 30 minutes -> 1h30m

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_format_expire(5400)).to_equal("1h30m")
```

</details>

#### 45 seconds -> 45s

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_format_expire(45)).to_equal("45s")
```

</details>

#### 12h34m56s mixed

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_format_expire(12 * 3600 + 34 * 60 + 56)).to_equal("12h34m56s")
```

</details>

#### zero -> 0s

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_format_expire(0)).to_equal("0s")
```

</details>

#### exit code mapping

#### 0 is success

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_mc_success(0)).to_equal(true)
```

</details>

#### 1 (generic failure) is not success

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_mc_success(1)).to_equal(false)
```

</details>

#### 2 (invalid args) is not success

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_mc_success(2)).to_equal(false)
```

</details>

#### NDJSON parsing

#### splits lines and parses each as JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ndjson = "{\"alias\":\"a\"}\n{\"alias\":\"b\"}\n"
val lines = _parse_ndjson_lines(ndjson)
expect(lines.len()).to_equal(2)
```

</details>

#### skips empty lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ndjson = "\n{\"alias\":\"a\"}\n\n"
val lines = _parse_ndjson_lines(ndjson)
expect(lines.len()).to_equal(1)
```

</details>

#### skips invalid JSON lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ndjson = "not json\n{\"alias\":\"ok\"}\n"
val lines = _parse_ndjson_lines(ndjson)
expect(lines.len()).to_equal(1)
```

</details>

#### ls entry parsing

#### extracts key + size + lastModified + etag

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ndjson = "{\"key\":\"zynq/v1/fw.bin\",\"type\":\"file\",\"size\":1048576,\"lastModified\":\"2026-04-01T10:00:00Z\",\"etag\":\"abc\"}"
val lines = _parse_ndjson_lines(ndjson)
expect(lines.len()).to_equal(1)
val entry = _entry_from_obj(lines[0])
expect(entry.key).to_equal("zynq/v1/fw.bin")
expect(entry.type).to_equal("file")
expect(entry.size).to_equal(1048576)
expect(entry.last_modified).to_equal("2026-04-01T10:00:00Z")
expect(entry.etag).to_equal("abc")
```

</details>

#### stat parsing

#### extracts name + size + lastModified

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ndjson = "{\"name\":\"a/b/key.bin\",\"type\":\"object\",\"size\":42,\"lastModified\":\"2026-04-25T00:00:00Z\",\"etag\":\"xyz\"}"
val lines = _parse_ndjson_lines(ndjson)
val s = _stat_from_obj(lines[0])
expect(s.name).to_equal("a/b/key.bin")
expect(s.size).to_equal(42)
expect(s.etag).to_equal("xyz")
```

</details>

#### share URL extraction

#### reads `share` field

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ndjson = "{\"status\":\"success\",\"share\":\"https://x/y?X-Amz-Signature=abc\"}"
val lines = _parse_ndjson_lines(ndjson)
val url = _share_url_from_obj(lines[0])
expect(url.starts_with("https://x/y?")).to_equal(true)
expect(url.contains("X-Amz-Signature=")).to_equal(true)
```

</details>

#### falls back to `url` field

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ndjson = "{\"status\":\"success\",\"url\":\"https://fallback/path\"}"
val lines = _parse_ndjson_lines(ndjson)
expect(_share_url_from_obj(lines[0])).to_equal("https://fallback/path")
```

</details>

#### admin info parsing

#### extracts mode and version from top object

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ndjson = "{\"mode\":\"online\",\"version\":\"2025-01-01T00-00-00Z\",\"region\":\"us-east-1\",\"deploymentID\":\"d-1\"}"
val lines = _parse_ndjson_lines(ndjson)
val info = _server_info_from_obj(lines[0])
expect(info.mode).to_equal("online")
expect(info.version).to_equal("2025-01-01T00-00-00Z")
expect(info.region).to_equal("us-east-1")
expect(info.deployment_id).to_equal("d-1")
```

</details>

#### McClient defaults

#### default mc_path is `mc`

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = McClient.default("myaistor")
expect(client.mc_path).to_equal("mc")
expect(client.alias_name).to_equal("myaistor")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/itf/adapter_minio_mc_spec.spl` |
| Updated | 2026-07-19 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MinIO mc adapter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
