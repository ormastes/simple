# Claude Full Sentry Error Boundary

> Checks children render before errors and null render after errors.

<!-- sdn-diagram:id=SentryErrorBoundary_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=SentryErrorBoundary_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

SentryErrorBoundary_spec -> std
SentryErrorBoundary_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=SentryErrorBoundary_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Sentry Error Boundary

Checks children render before errors and null render after errors.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/SentryErrorBoundary_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks children render before errors and null render after errors.

## Scenarios

### Claude full SentryErrorBoundary

#### renders children until an error is captured

- Initial state has no error and renders children
   - Expected: boundary.hasError equals `initialHasError()`
   - Expected: boundary.render() equals `child`
- boundary captureError
   - Expected: boundary.hasError equals `errorStateHasError()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Initial state has no error and renders children")
val boundary = SentryErrorBoundary.new("child")
expect(boundary.hasError).to_equal(initialHasError())
expect(boundary.render()).to_equal("child")
boundary.captureError()
expect(boundary.hasError).to_equal(errorStateHasError())
expect(boundary.render()).to_be_nil()
```

</details>

#### exports source-backed constants

- Pin boundary behavior
   - Expected: rendersNullAfterError() is true
   - Expected: rendersChildrenBeforeError() is true
   - Expected: sentryErrorBoundarySourceLinesModeled() equals `26`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin boundary behavior")
expect(rendersNullAfterError()).to_equal(true)
expect(rendersChildrenBeforeError()).to_equal(true)
expect(sentryErrorBoundarySourceLinesModeled()).to_equal(26)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
