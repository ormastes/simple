# Claude Full WebFetchTool Utils

> Checks the strict parity surface for WebFetchTool utility errors and policies.

<!-- sdn-diagram:id=utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

utils_spec -> std
utils_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=utils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full WebFetchTool Utils

Checks the strict parity surface for WebFetchTool utility errors and policies.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/tools/WebFetchTool/utils_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks the strict parity surface for WebFetchTool utility errors and policies.

## Scenarios

### Claude full WebFetchTool utils

#### should expose domain blocking errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocked = DomainBlockedError.new("blocked.example")
expect(blocked.name).to_equal("DomainBlockedError")
expect(blocked.message).to_equal("Claude Code is unable to fetch from blocked.example")
val failed = DomainCheckFailedError.new("unknown.example")
expect(failed.name).to_equal("DomainCheckFailedError")
expect(failed.message).to_contain("Unable to verify if domain unknown.example is safe to fetch")
val egress = EgressBlockedError.new("proxy.example")
expect(egress.name).to_equal("EgressBlockedError")
expect(egress.message).to_contain("\"error_type\":\"EGRESS_BLOCKED\"")
```

</details>

#### should validate URLs and redirect policy

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(validateURL("https://example.com/path")).to_equal(true)
expect(validateURL("http://example.com/path")).to_equal(true)
expect(validateURL("file:///tmp/a")).to_equal(false)
expect(validateURL("https://user@example.com/path")).to_equal(false)
expect(validateURL("https://localhost/path")).to_equal(false)
expect(isPermittedRedirect("https://example.com/a", "https://www.example.com/b")).to_equal(true)
expect(isPermittedRedirect("https://example.com/a", "http://example.com/b")).to_equal(false)
expect(isPermittedRedirect("https://example.com/a", "https://evil.example/b")).to_equal(false)
```

</details>

#### should expose cache constants and helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cleared = clearWebFetchCache(WebFetchCacheState.new(2, 3))
expect(cleared.urlEntries).to_equal(0)
expect(cleared.domainEntries).to_equal(0)
expect(cacheTtlMs()).to_equal(900000)
expect(maxCacheSizeBytes()).to_equal(52428800)
expect(maxHttpContentLength()).to_equal(10485760)
expect(fetchTimeoutMs()).to_equal(60000)
expect(domainCheckTimeoutMs()).to_equal(10000)
expect(maxRedirects()).to_equal(10)
expect(maxMarkdownLength()).to_equal(100000)
expect(isPreapprovedUrl("https://docs.anthropic.com/en/docs")).to_equal(true)
expect(upgradedUrl("http://example.com/a")).to_equal("https://example.com/a")
expect(webFetchUtilsSourceLinesModeled()).to_equal(530)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
