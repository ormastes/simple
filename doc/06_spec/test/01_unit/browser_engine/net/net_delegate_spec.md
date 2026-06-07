# NetDelegate and FetchDispatch Interface Specification

> Verifies the lazy seam interfaces: NoopNetDelegate returns an empty response, FetchDispatch nullable slot on ScriptHost defaults to none, and BrowserRenderer.navigate() entry point exists and calls net_delegate.navigate(). No network calls — pure interface/entity checks.

<!-- sdn-diagram:id=net_delegate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=net_delegate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

net_delegate_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=net_delegate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NetDelegate and FetchDispatch Interface Specification

Verifies the lazy seam interfaces: NoopNetDelegate returns an empty response, FetchDispatch nullable slot on ScriptHost defaults to none, and BrowserRenderer.navigate() entry point exists and calls net_delegate.navigate(). No network calls — pure interface/entity checks.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #M16-AC2, #M16-AC7, #M16-AC8 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Draft |
| Source | `test/01_unit/browser_engine/net/net_delegate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the lazy seam interfaces: NoopNetDelegate returns an empty response,
FetchDispatch nullable slot on ScriptHost defaults to none, and
BrowserRenderer.navigate() entry point exists and calls net_delegate.navigate().
No network calls — pure interface/entity checks.

## Scenarios

### NoopNetDelegate

#### AC-7: NoopNetDelegate.navigate returns a FetchResponse

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val noop = NoopNetDelegate.new()
val resp = noop.navigate(make_test_url())
val has_status = (resp.status >= 0)
expect(has_status).to_equal(true)
```

</details>

#### AC-7: NoopNetDelegate.navigate returns status 0 (no network)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val noop = NoopNetDelegate.new()
val resp = noop.navigate(make_test_url())
expect(resp.status).to_equal(0)
```

</details>

#### AC-7: NoopNetDelegate.navigate returns empty body

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val noop = NoopNetDelegate.new()
val resp = noop.navigate(make_test_url())
expect(resp.body.length).to_equal(0)
```

</details>

#### AC-7: NoopNetDelegate.fetch returns status 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val noop = NoopNetDelegate.new()
val resp = noop.fetch(make_test_request())
expect(resp.status).to_equal(0)
```

</details>

#### AC-7: NoopNetDelegate.fetch returns empty body

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val noop = NoopNetDelegate.new()
val resp = noop.fetch(make_test_request())
expect(resp.body.length).to_equal(0)
```

</details>

### ScriptHost fetch_dispatch field

#### AC-2: ScriptHost.fetch_dispatch is none by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host = ScriptHost.new()
val has_dispatch = host.fetch_dispatch.is_some()
expect(has_dispatch).to_equal(false)
```

</details>

#### AC-2: set_fetch_dispatch makes fetch_dispatch non-nil

1. host set fetch dispatch
   - Expected: has_dispatch is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host = ScriptHost.new()
val dispatch = make_noop_dispatch()
host.set_fetch_dispatch(dispatch)
val has_dispatch = host.fetch_dispatch.is_some()
expect(has_dispatch).to_equal(true)
```

</details>

### BrowserRenderer net_delegate field

#### AC-7: BrowserRenderer.net_delegate is none by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val renderer = BrowserRenderer.new()
val has_delegate = renderer.net_delegate.is_some()
expect(has_delegate).to_equal(false)
```

</details>

#### AC-7: set_net_delegate makes net_delegate non-nil

1. renderer set net delegate
   - Expected: has_delegate is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val renderer = BrowserRenderer.new()
val noop = NoopNetDelegate.new()
renderer.set_net_delegate(noop)
val has_delegate = renderer.net_delegate.is_some()
expect(has_delegate).to_equal(true)
```

</details>

#### AC-8: navigate() method exists on BrowserRenderer

1. renderer set net delegate
   - Expected: resp.status equals `0`
   - Expected: resp.body.length equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val renderer = BrowserRenderer.new()
val noop = NoopNetDelegate.new()
renderer.set_net_delegate(noop)
val resp = renderer.navigate("https://example.com/")
expect(resp.status).to_equal(0)
expect(resp.body.length).to_equal(0)
```

</details>

#### AC-8: navigate() with no net_delegate does not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val renderer = BrowserRenderer.new()
val resp = renderer.navigate("https://example.com/")
expect(resp.status).to_equal(0)
expect(renderer.net_delegate.is_some()).to_equal(false)
```

</details>

### FetchResponse body field

#### AC-4: FetchResponse.body is a [u8] array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = make_response_with_text_body("hello world")
expect(resp.body.length).to_be_greater_than(0)
```

</details>

#### AC-4: body_text() decodes [u8] to text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = make_response_with_text_body("hello world")
expect(resp.body_text()).to_equal("hello world")
```

</details>

#### AC-4: FetchResponse with empty body has length 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = make_empty_response()
expect(resp.body.length).to_equal(0)
```

</details>

#### AC-4: body_text() on empty body returns empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resp = make_empty_response()
expect(resp.body_text()).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
