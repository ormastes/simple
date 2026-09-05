# in-guest HTTP route classification + hardening (Lane C2)

> Proves the boot HTTP server's routing and request hardening in-process,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# in-guest HTTP route classification + hardening (Lane C2)

Proves the boot HTTP server's routing and request hardening in-process,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/net/http_route_spec.spl` |
| Updated | 2026-07-19 |
| Generator | `simple spipe-docgen` (Simple) |

Proves the boot HTTP server's routing and request hardening in-process,
without a socket or a mounted disk, by driving the pure classifier
(src/os/kernel/net/http_route.spl) that both boot transports
(src/os/kernel/boot/http_baremetal.spl and src/os/kernel/net/http_baremetal.spl)
sit on top of.

The classifier reuses the REAL Simple web server pipeline
(std.nogc_sync_mut.http_server): parse_request_line for the request line and
path_is_safe for the traversal check. These specs assert the three-route
decision (GET /, GET /health, and GET /files/<name>) plus fail-closed handling of
malformed, non-GET, unknown-route, nested, and path-traversal requests.

## Scenarios

### http route: happy paths

#### GET / classifies as Status

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val route = http_classify_request("GET / HTTP/1.1\r\nHost: x\r\n\r\n")
match route.kind:
    HttpRouteKind.Status: expect(true).to_equal(true)
    _: expect("status").to_equal("other")
```

</details>

#### GET /health classifies as Health

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val route = http_classify_request("GET /health HTTP/1.1\r\nHost: x\r\n\r\n")
match route.kind:
    HttpRouteKind.Health: expect(true).to_equal(true)
    _: expect("health").to_equal("other")
```

</details>

#### GET /files/<name> classifies as File with a rooted path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val route = http_classify_request("GET /files/VERSION.TXT HTTP/1.1\r\n\r\n")
match route.kind:
    HttpRouteKind.File: expect(route.file_path).to_equal("/VERSION.TXT")
    _: expect("file").to_equal("other")
```

</details>

### http route: fail-closed hardening

#### a malformed request line is BadRequest

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match _kind("GARBAGE\r\n\r\n"):
    HttpRouteKind.BadRequest: expect(true).to_equal(true)
    _: expect("badrequest").to_equal("other")
```

</details>

#### a request with no HTTP version is BadRequest

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match _kind("GET /\r\n\r\n"):
    HttpRouteKind.BadRequest: expect(true).to_equal(true)
    _: expect("badrequest").to_equal("other")
```

</details>

#### a non-GET method is NotFound

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match _kind("POST / HTTP/1.1\r\n\r\n"):
    HttpRouteKind.NotFound: expect(true).to_equal(true)
    _: expect("notfound").to_equal("other")
```

</details>

#### an unknown route is NotFound

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match _kind("GET /nope HTTP/1.1\r\n\r\n"):
    HttpRouteKind.NotFound: expect(true).to_equal(true)
    _: expect("notfound").to_equal("other")
```

</details>

#### an empty /files/ name is NotFound

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match _kind("GET /files/ HTTP/1.1\r\n\r\n"):
    HttpRouteKind.NotFound: expect(true).to_equal(true)
    _: expect("notfound").to_equal("other")
```

</details>

#### a nested /files/ path (extra segment) is NotFound

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match _kind("GET /files/sub/file.txt HTTP/1.1\r\n\r\n"):
    HttpRouteKind.NotFound: expect(true).to_equal(true)
    _: expect("notfound").to_equal("other")
```

</details>

#### a dot-dot traversal under /files/ is NotFound

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match _kind("GET /files/../etc/passwd HTTP/1.1\r\n\r\n"):
    HttpRouteKind.NotFound: expect(true).to_equal(true)
    _: expect("notfound").to_equal("other")
```

</details>

#### an encoded dot-dot traversal under /files/ is NotFound

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match _kind("GET /files/..%2fpasswd HTTP/1.1\r\n\r\n"):
    HttpRouteKind.NotFound: expect(true).to_equal(true)
    _: expect("notfound").to_equal("other")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
