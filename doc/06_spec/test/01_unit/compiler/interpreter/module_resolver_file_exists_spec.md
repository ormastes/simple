# Module Resolver rt_file_exists Bool/i64 Regression (B5)

> Regression for: rt_file_exists_bool_vs_int_interpreted_resolver_2026-06-10

<!-- sdn-diagram:id=module_resolver_file_exists_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=module_resolver_file_exists_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

module_resolver_file_exists_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=module_resolver_file_exists_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Resolver rt_file_exists Bool/i64 Regression (B5)

Regression for: rt_file_exists_bool_vs_int_interpreted_resolver_2026-06-10

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/module_resolver_file_exists_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Regression for: rt_file_exists_bool_vs_int_interpreted_resolver_2026-06-10

In the interpreter the `extern fn rt_file_exists` returns a native Rust `bool`
(true/false).  The resolver previously compared `rt_file_exists(path) == 1`
which always failed for `true`, causing all path candidates to be rejected.

The fix: declare the return type as `bool` and use the result directly as a
condition (no `== 1`).

This spec drives the resolver directly and verifies that known-good stdlib paths
resolve to non-empty strings — confirming the bool-path is taken correctly.

## Scenarios

### module_resolver rt_file_exists bool regression

#### resolves std.ctype to a non-empty path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = check_std_ctype_resolves()
expect(err).to_equal("")
```

</details>

#### resolves std.io_runtime to a non-empty path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = check_std_io_runtime_resolves()
expect(err).to_equal("")
```

</details>

#### returns non-empty fallback path for unknown module

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = check_nonexistent_returns_nonempty_fallback()
expect(err).to_equal("")
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
