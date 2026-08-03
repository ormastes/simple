# Release Beta Detail Design

## Evidence contract

`check-release-beta-readiness.shs` is the local aggregate. It never builds or invents evidence; it validates an evidence directory containing provenance-bound receipts produced by the strict bootstrap, platform jobs, checker contracts, whole tests, and GitHub Actions.

| Receipt | Required fields |
|---|---|
| `bootstrap.env` | revision, Stage 2/3/4 status, fallback disabled, Stage 4 path/hash, elapsed time, max RSS |
| `essential_tools.env` | exact Stage 4 hash; test/lint/duplicate/aggregate statuses |
| `release_checkers.env` | executable/payload/SimpleOS/MCP checker statuses |
| `platforms.env` | one status/artifact/checksum for each selected non-macOS row |
| `verification.env` | core/lib/MCP/LSP, runtime guards, whole-test, spec-layout, docs, verify status |
| `github_release.env` | workflow run id/url, revision, conclusion, published tag status, prerelease status |

The aggregate rejects missing files, duplicate keys, non-`pass` required statuses, revision/hash mismatches, source-only artifacts in executable roles, unknown platform rows, and a GitHub conclusion other than `success`.

## Flow

1. Bootstrap emits Stage receipts only after provenance and sanity admission.
2. `record-release-beta-essential-tools.shs` runs the canonical smoke on the exact Stage 4 path, requires every real marker, retains the log, and writes a receipt bound to that executable hash.
3. Platform producers validate packages before upload and embed an exact revision/version/platform/role manifest. `collect-release-beta-platform-evidence.shs` revalidates downloaded archives and materializes their checksums into `platforms.env`.
4. The release workflow independently runs the canonical full FreeBSD QEMU bootstrap. Its success is a publication dependency rather than an annotation on a cross-built archive.
5. The GitHub release job downloads named required artifacts, validates them, and publishes. After the job completes, `record-release-beta-github-evidence.shs` queries GitHub for the exact run revision, successful conclusion, and published tag before writing the remote receipt.
6. The aggregate checker binds all receipts to one revision/version and emits `release_beta_readiness_status=pass` only when every selected requirement is proven.

## Error handling

- Missing/malformed evidence: exit nonzero with `reason=missing-*` or `reason=malformed-*`.
- Mismatched revision/hash/version: exit nonzero with both expected and observed values.
- Unsupported host row: remains `blocked`, never `pass` or omitted.
- MacOS rows: excluded from required execution only; malformed retained workflow wiring is still rejected by workflow validation.

## Performance

The bootstrap receipt records elapsed seconds and maximum RSS per stage. Facade traversal retains the shallowest visit depth per root; no global cache survives between independent imports. Per-expression and flat-statement bootstrap print probes are excluded from release builds because their unbuffered output distorts both timing and memory evidence. The aggregate caps isolated Stage 3 at 254 seconds (the rounded 253.9-second retained baseline) and each stage at 24 GiB maximum RSS without rerunning green builds. `RELEASE_BETA_STAGE3_ELAPSED_CEILING_SECONDS` and `RELEASE_BETA_STAGE_MAX_RSS_CEILING_KB` exist for diagnostic experiments, not silent release-policy changes.
