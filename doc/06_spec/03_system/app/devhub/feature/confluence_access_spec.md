# Confluence Access Specification

> Tests covering Confluence access with offline transport fixtures, REQ-CONFLUENCE-ACCESS-001: deployment routing, REQ-CONFLUENCE-ACCESS-002: literal search values, REQ-CONFLUENCE-ACCESS-003: decoded response content, REQ-CONFLUENCE-ACCESS-004: transport response and diagnostics, REQ-CONFLUENCE-ACCESS-005: target credential isolation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Confluence Access Specification

## Scenarios

### Confluence access with offline transport fixtures

### REQ-CONFLUENCE-ACCESS-001: deployment routing

#### should retain Cloud wiki and Data Center context paths

- Load shared configuration
- Resolve Confluence access
   - Expected: confluence_content_root(cloud) equals `https://site.atlassian.net/wiki/rest/api/content`
   - Expected: confluence_content_root(dc) equals `https://dc.example:8090/confluence/rest/api/content`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load shared configuration")
val cloud = _apply_config_value(ItfConfig.default(), "confluence", "url", "https://site.atlassian.net/wiki/")
val dc = _apply_config_value(ItfConfig.default(), "confluence", "url", "https://dc.example:8090/confluence/")
step("Resolve Confluence access")
expect(confluence_content_root(cloud)).to_equal("https://site.atlassian.net/wiki/rest/api/content")
expect(confluence_content_root(dc)).to_equal("https://dc.example:8090/confluence/rest/api/content")
```

</details>

#### should treat the gateway as the complete API prefix

- Load shared configuration
- Resolve Confluence access
   - Expected: confluence_content_root(config) equals `https://gateway.example/proxy/wiki/content`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load shared configuration")
val config = _apply_config_value(ItfConfig.default(), "confluence", "gateway_url", "https://gateway.example/proxy/wiki/")
step("Resolve Confluence access")
expect(confluence_content_root(config)).to_equal("https://gateway.example/proxy/wiki/content")
```

</details>

#### should report missing URL without inventing a target

- Resolve Confluence access
   - Expected: confluence_content_root(ItfConfig.default()) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve Confluence access")
expect(confluence_content_root(ItfConfig.default())).to_equal("")
```

</details>

### REQ-CONFLUENCE-ACCESS-002: literal search values

#### should build ordinary title and space searches

- Resolve Confluence access
   - Expected: confluence_search_cql("guide", "ENG") equals `type=page and title~"guide" and space="ENG"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve Confluence access")
expect(confluence_search_cql("guide", "ENG")).to_equal("type=page and title~\"guide\" and space=\"ENG\"")
```

</details>

#### should preserve literal backslashes and quotes in both fields

- Resolve Confluence access
   - Expected: confluence_search_cql("a\\\"b", "x\\\"y") equals `type=page and title~"a\\\\\\"b" and space="x\\\\\\"y"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve Confluence access")
expect(confluence_search_cql("a\\\"b", "x\\\"y")).to_equal("type=page and title~\"a\\\\\\\"b\" and space=\"x\\\\\\\"y\"")
```

</details>

#### should keep a quoted space value from becoming a CQL clause

- Execute the request
   - Expected: cql equals `type=page and title~"" and space="ENG\\" or type=blogpost or space=\\"OPS"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Execute the request")
val cql = confluence_search_cql("", "ENG\" or type=blogpost or space=\"OPS")
val argv = _confluence_curl_argv("", "GET", "https://fixture.invalid/content/search", "", ["cql={cql}"])
expect(cql).to_equal("type=page and title~\"\" and space=\"ENG\\\" or type=blogpost or space=\\\"OPS\"")
expect(argv).to_contain("cql={cql}")
expect(argv).to_contain("--data-urlencode")
```

</details>

### REQ-CONFLUENCE-ACCESS-003: decoded response content

#### should return decoded storage text with quotes and newlines

- Execute the request
- Check response and redaction
   - Expected: _json_str(body, "value") equals `<p title="guide">line1\nline2</p>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Execute the request")
val body = json_parse("\{\"value\":\"<p title=\\\"guide\\\">line1\\nline2</p>\"\}")
step("Check response and redaction")
expect(_json_str(body, "value")).to_equal("<p title=\"guide\">line1\nline2</p>")
```

</details>

#### should preserve an empty result page

- Execute the request
- Check response and redaction
   - Expected: ok is true
   - Expected: items.len() equals `0`
   - Expected: raw equals `\{"results":[]\}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Execute the request")
val (ok, items, raw) = _parse_results("\{\"results\":[]\}")
step("Check response and redaction")
expect(ok).to_equal(true)
expect(items.len()).to_equal(0)
expect(raw).to_equal("\{\"results\":[]\}")
```

</details>

#### should reject malformed listing shapes instead of claiming no pages

- Execute the request
- Check response and redaction
   - Expected: ok is false
   - Expected: items.len() equals `0`
   - Expected: message equals `invalid Confluence response: results must be an array`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Execute the request")
for body in ["\{\}", "\{\"results\":\"unavailable\"\}"]:
    val (ok, items, message) = _parse_results(body)
    step("Check response and redaction")
    expect(ok).to_equal(false)
    expect(items.len()).to_equal(0)
    expect(message).to_equal("invalid Confluence response: results must be an array")
```

</details>

### REQ-CONFLUENCE-ACCESS-004: transport response and diagnostics

#### should preserve successful content including words resembling secrets

- Execute the request
- Check response and redaction
   - Expected: status equals `200`
   - Expected: body equals `password-field: documentation example`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Execute the request")
val (status, body) = confluence_response_result("password-field: documentation example\n200", "", 0)
step("Check response and redaction")
expect(status).to_equal(200)
expect(body).to_equal("password-field: documentation example")
```

</details>

#### should redact HTTP failures and preserve their status without retry

- Execute the request
- Check response and redaction
   - Expected: status equals `code`
   - Expected: body equals `Authorization: ***`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Execute the request")
for code in [401, 429, 503]:
    val (status, body) = confluence_response_result("Authorization: Bearer fixture-secret\n{code}", "", 0)
    step("Check response and redaction")
    expect(status).to_equal(code)
    expect(body).to_equal("Authorization: ***")
```

</details>

#### should redact transport failures even when stdout carries a success status

- Execute the request
- Check response and redaction
   - Expected: status equals `0`
   - Expected: body equals `transport error: Authorization: ***`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Execute the request")
val (status, body) = confluence_response_result("partial\n200", "Authorization: Bearer fixture-secret", 7)
step("Check response and redaction")
expect(status).to_equal(0)
expect(body).to_equal("transport error: Authorization: ***")
```

</details>

#### should reject absent and malformed HTTP status trailers

- Execute the request
- Check response and redaction
   - Expected: status equals `0`
   - Expected: body equals `transport error: curl exit 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Execute the request")
for stdout in ["", "body\nabc", "body\n20"]:
    val (status, body) = confluence_response_result(stdout, "", 0)
    step("Check response and redaction")
    expect(status).to_equal(0)
    expect(body).to_equal("transport error: curl exit 0")
```

</details>

### REQ-CONFLUENCE-ACCESS-005: target credential isolation

#### should select only the named target token from the auth document

- Load shared configuration
   - Expected: dir_create_all("build/confluence-access-fixture") is true
   - Expected: file_write(path, "confluence:\n    token: global-fixture\nconfluence.team:\n    token: team-fixture\n") is true
- Resolve Confluence access
- Execute the request
- Check response and redaction
   - Expected: token equals `team-fixture`
   - Expected: argv does not contain `Authorization: Bearer global-fixture`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load shared configuration")
expect(dir_create_all("build/confluence-access-fixture")).to_equal(true)
val path = "build/confluence-access-fixture/auth.sdn"
expect(file_write(path, "confluence:\n    token: global-fixture\nconfluence.team:\n    token: team-fixture\n")).to_equal(true)
val config = ItfConfig(confluence_target: "team", token_envs: [], token_cmds: [])
step("Resolve Confluence access")
val token = resolve_auth_token_from(config, "confluence", path)
step("Execute the request")
val argv = _confluence_curl_argv(atlassian_auth_header("bearer", "", token), "GET", "https://fixture.invalid/content", "", [])
step("Check response and redaction")
expect(token).to_equal("team-fixture")
expect(argv).to_contain("Authorization: Bearer team-fixture")
expect(argv.contains("Authorization: Bearer global-fixture")).to_equal(false)
```

</details>

#### should preserve legacy default credentials when no target is selected

- Load shared configuration
   - Expected: dir_create_all("build/confluence-access-fixture") is true
   - Expected: file_write(path, "confluence:\n    token: legacy-fixture\n") is true
- Resolve Confluence access
   - Expected: resolve_auth_token_from(ItfConfig.default(), "confluence", path) equals `legacy-fixture`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load shared configuration")
expect(dir_create_all("build/confluence-access-fixture")).to_equal(true)
val path = "build/confluence-access-fixture/legacy-auth.sdn"
expect(file_write(path, "confluence:\n    token: legacy-fixture\n")).to_equal(true)
step("Resolve Confluence access")
expect(resolve_auth_token_from(ItfConfig.default(), "confluence", path)).to_equal("legacy-fixture")
```

</details>

#### should reject missing named credentials despite a global token

- Load shared configuration
   - Expected: dir_create_all("build/confluence-access-fixture") is true
   - Expected: file_write(path, "confluence:\n    token: unrelated-fixture\n") is true
- Resolve Confluence access
- Check response and redaction
   - Expected: token equals ``
   - Expected: atlassian_auth_header("bearer", "", token) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load shared configuration")
expect(dir_create_all("build/confluence-access-fixture")).to_equal(true)
val path = "build/confluence-access-fixture/missing-auth.sdn"
expect(file_write(path, "confluence:\n    token: unrelated-fixture\n")).to_equal(true)
val config = ItfConfig(confluence_target: "missing", token_envs: [], token_cmds: [])
step("Resolve Confluence access")
val token = resolve_auth_token_from(config, "confluence", path)
step("Check response and redaction")
expect(token).to_equal("")
expect(atlassian_auth_header("bearer", "", token)).to_equal("")
```

</details>

#### should prefer the scoped environment token over the file token

- Load shared configuration
   - Expected: dir_create_all("build/confluence-access-fixture") is true
   - Expected: file_write(path, "confluence.team:\n    token: file-fixture\n") is true
- Resolve Confluence access
- Check response and redaction
   - Expected: configured is true
   - Expected: restored is true
   - Expected: token equals `scoped-env-fixture`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load shared configuration")
expect(dir_create_all("build/confluence-access-fixture")).to_equal(true)
val path = "build/confluence-access-fixture/env-auth.sdn"
expect(file_write(path, "confluence.team:\n    token: file-fixture\n")).to_equal(true)
val key = "SIMPLE_CONFLUENCE_ACCESS_FIXTURE_TOKEN"
val was_set = env_has(key)
val previous = env_get(key)
val configured = env_set(key, " scoped-env-fixture ")
val config = ItfConfig(confluence_target: "team", token_envs: [("confluence.team", key)], token_cmds: [])
step("Resolve Confluence access")
val token = resolve_auth_token_from(config, "confluence", path)
val restored = if was_set: env_set(key, previous) else: env_unset(key)
step("Check response and redaction")
expect(configured).to_equal(true)
expect(restored).to_equal(true)
expect(token).to_equal("scoped-env-fixture")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/devhub/feature/confluence_access_spec.spl` |
| Updated | 2026-10-02 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Confluence access with offline transport fixtures, REQ-CONFLUENCE-ACCESS-001: deployment routing, REQ-CONFLUENCE-ACCESS-002: literal search values, REQ-CONFLUENCE-ACCESS-003: decoded response content, REQ-CONFLUENCE-ACCESS-004: transport response and diagnostics, REQ-CONFLUENCE-ACCESS-005: target credential isolation.
- Confluence access with offline transport fixtures
- REQ-CONFLUENCE-ACCESS-001: deployment routing
- REQ-CONFLUENCE-ACCESS-002: literal search values
- REQ-CONFLUENCE-ACCESS-003: decoded response content
- REQ-CONFLUENCE-ACCESS-004: transport response and diagnostics
- REQ-CONFLUENCE-ACCESS-005: target credential isolation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
