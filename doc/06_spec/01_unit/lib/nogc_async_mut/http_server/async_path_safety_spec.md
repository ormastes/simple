# Async HTTP Router — path traversal rejected before any handler

> The async router must reject traversal/escape paths BEFORE location matching, so neither the inline static handler nor any dynamic handler ever sees an unsafe path. The guard is the shared `std.common.net.http_core.path_is_safe` — the same one the sync router uses — so the two transports cannot drift. The worker additionally re-checks the path in its inline static handler before concatenating `root + path` (defence in depth), and maps a router rejection to a 400 response rather than a 404.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async HTTP Router — path traversal rejected before any handler

The async router must reject traversal/escape paths BEFORE location matching, so neither the inline static handler nor any dynamic handler ever sees an unsafe path. The guard is the shared `std.common.net.http_core.path_is_safe` — the same one the sync router uses — so the two transports cannot drift. The worker additionally re-checks the path in its inline static handler before concatenating `root + path` (defence in depth), and maps a router rejection to a 400 response rather than a 404.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Design | N/A |
| Research | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Source | `test/01_unit/lib/nogc_async_mut/http_server/async_path_safety_spec.spl` |
| Updated | 2026-08-14 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The async router must reject traversal/escape paths BEFORE location matching,
so neither the inline static handler nor any dynamic handler ever sees an
unsafe path. The guard is the shared `std.common.net.http_core.path_is_safe`
— the same one the sync router uses — so the two transports cannot drift.
The worker additionally re-checks the path in its inline static handler
before concatenating `root + path` (defence in depth), and maps a router
rejection to a 400 response rather than a 404.

## Rejected path shapes

| Shape | Example |
|-------|---------|
| Dot-dot segment | `/static/../etc/passwd` |
| Encoded dot-dot | `/static/%2e%2e/secret` |
| Encoded-slash traversal | `/..%2fsecret` |
| Double-slash bypass | `//etc/passwd` |
| Null-byte injection | `/index.html%00.png` |

Legitimate names that merely contain dots (`/release..notes.txt`) stay
routable.

## Examples

```simple
val router = AsyncRouter.new([static_root_location])
val r = router.route(request_for("/../x"))
# Err(ParseError("400 Bad Request: unsafe path")) — no location was matched
```

## Troubleshooting

- A 400 with "unsafe path" means the traversal guard fired at the router;
  the request never reached location matching or any handler.
- If a path you consider legitimate is rejected, check it against the
  shared `path_is_safe` corpus in `http_core_spec` — the rule set is
  deliberately identical across transports.

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Design:** N/A
**Research:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md

Lane: .spipe/simple_enterprise_suite (Wave A, AC-3).

## Scenarios

### async router — unsafe paths never reach a handler

#### routes a normal path to the static location

- Configure a catch-all static location
- Route a safe document path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Configure a catch-all static location")
val router = AsyncRouter.new([make_static_root()])
step("Route a safe document path")
expect(route_rejected(router, "/index.html")).to_be(false)
```

</details>

#### rejects a dot-dot traversal path

- Route a traversal path aimed below the document root


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val router = AsyncRouter.new([make_static_root()])
step("Route a traversal path aimed below the document root")
expect(route_rejected(router, "/static/../etc/passwd")).to_be(true)
```

</details>

#### rejects an encoded dot-dot traversal path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val router = AsyncRouter.new([make_static_root()])
expect(route_rejected(router, "/static/%2e%2e/secret")).to_be(true)
```

</details>

#### rejects an encoded-slash traversal path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val router = AsyncRouter.new([make_static_root()])
expect(route_rejected(router, "/..%2fsecret")).to_be(true)
```

</details>

#### rejects a double-slash bypass path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val router = AsyncRouter.new([make_static_root()])
expect(route_rejected(router, "//etc/passwd")).to_be(true)
```

</details>

#### rejects a null-byte injection path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val router = AsyncRouter.new([make_static_root()])
expect(route_rejected(router, "/index.html%00.png")).to_be(true)
```

</details>

#### rejects the unsafe path even when a matching location exists

- Verify rejection happens BEFORE location matching
- Ok
- fail
- Err
- HttpServerError ParseError
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify rejection happens BEFORE location matching")
# The catch-all "/" prefix would match "/../x" if matching ran first;
# the guard must fire before any location is considered.
val router = AsyncRouter.new([make_static_root()])
val r = router.route(make_request("/../x"))
match r:
    Ok(_):
        fail("unsafe path was routed to a location")
    Err(e):
        match e:
            HttpServerError.ParseError(msg):
                expect(msg.starts_with("400")).to_be(true)
            _:
                fail("expected ParseError(400 ...) for unsafe path")
```

</details>

#### still allows dots inside legitimate filenames

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val router = AsyncRouter.new([make_static_root()])
expect(route_rejected(router, "/release..notes.txt")).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/simple_erp.md`
- **Research:** `doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md`


</details>
