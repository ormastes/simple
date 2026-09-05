# Simple launcher dispatch regression spec

> Verifies `bin/simple` keeps the shell-wrapper routing for launcher-only

<!-- sdn-diagram:id=simple_launcher_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_launcher_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_launcher_dispatch_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_launcher_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple launcher dispatch regression spec

Verifies `bin/simple` keeps the shell-wrapper routing for launcher-only

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/simple_launcher_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies `bin/simple` keeps the shell-wrapper routing for launcher-only
entrypoints and honors explicit runtime selection for test-path execution.

## Scenarios

### simple launcher dispatch

#### routes duplicate-check through the release runtime entrypoint

1. make fake runtime
   - Expected: code equals `0`
   - Expected: stderr equals ``
2. expect arg
3. expect arg
4. expect arg
5. expect arg
6. expect arg


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = setup_repo_root("release_duplicate_check")
make_fake_runtime(root + "/bin/release/linux-x86_64/simple")

val (stdout, stderr, code) = run_wrapper(root, ["duplicate-check", "src/app", "--cosine"])

expect(code).to_equal(0)
expect(stderr).to_equal("")
expect_arg(stdout, 1, "run")
expect_arg(stdout, 2, root + "/src/compiler/90.tools/duplicate_check/main.spl")
expect_arg(stdout, 3, "duplicate-check")
expect_arg(stdout, 4, "src/app")
expect_arg(stdout, 5, "--cosine")
```

</details>

#### routes stats through the release runtime entrypoint

1. make fake runtime
   - Expected: code equals `0`
   - Expected: stderr equals ``
2. expect arg
3. expect arg
4. expect arg
5. expect arg
6. expect arg


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = setup_repo_root("release_stats")
make_fake_runtime(root + "/bin/release/linux-x86_64/simple")

val (stdout, stderr, code) = run_wrapper(root, ["stats", "--brief", "--json"])

expect(code).to_equal(0)
expect(stderr).to_equal("")
expect_arg(stdout, 1, "run")
expect_arg(stdout, 2, root + "/src/app/cli/stats_entry.spl")
expect_arg(stdout, 3, "stats")
expect_arg(stdout, 4, "--brief")
expect_arg(stdout, 5, "--json")
```

</details>

#### routes duplicate-check through the bootstrap runtime when release is absent

1. make fake runtime
   - Expected: code equals `0`
   - Expected: stderr equals ``
2. expect arg
3. expect arg
4. expect arg
5. expect arg


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = setup_repo_root("bootstrap_duplicate_check")
make_fake_runtime(root + "/src/compiler_rust/target/bootstrap/simple")

val (stdout, stderr, code) = run_wrapper(root, ["duplicate-check", "src/compiler"])

expect(code).to_equal(0)
expect(stderr).to_equal("")
expect_arg(stdout, 1, "run")
expect_arg(stdout, 2, root + "/src/compiler/90.tools/duplicate_check/main.spl")
expect_arg(stdout, 3, "duplicate-check")
expect_arg(stdout, 4, "src/compiler")
```

</details>

#### routes stats through the bootstrap runtime when release is absent

1. make fake runtime
   - Expected: code equals `0`
   - Expected: stderr equals ``
2. expect arg
3. expect arg
4. expect arg
5. expect arg


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = setup_repo_root("bootstrap_stats")
make_fake_runtime(root + "/src/compiler_rust/target/bootstrap/simple")

val (stdout, stderr, code) = run_wrapper(root, ["stats", "--quick"])

expect(code).to_equal(0)
expect(stderr).to_equal("")
expect_arg(stdout, 1, "run")
expect_arg(stdout, 2, root + "/src/app/cli/stats_entry.spl")
expect_arg(stdout, 3, "stats")
expect_arg(stdout, 4, "--quick")
```

</details>

#### passes normal commands straight through to the selected runtime

1. make fake runtime
   - Expected: code equals `0`
   - Expected: stderr equals ``
   - Expected: stdout does not contain `arg1=run\n`
2. expect arg
3. expect arg


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = setup_repo_root("release_passthrough")
make_fake_runtime(root + "/bin/release/linux-x86_64/simple")

val (stdout, stderr, code) = run_wrapper(root, ["check", "src/app/cli/main.spl"])

expect(code).to_equal(0)
expect(stderr).to_equal("")
expect(stdout.contains("arg1=run\n")).to_equal(false)
expect_arg(stdout, 1, "check")
expect_arg(stdout, 2, "src/app/cli/main.spl")
```

</details>

#### honors SIMPLE_BINARY for the test path

1. make fake runtime
2. make fake runtime
   - Expected: code equals `0`
   - Expected: stderr equals ``
3. expect arg
4. expect arg


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = setup_repo_root("test_path_simple_binary")
make_fake_runtime(root + "/src/compiler_rust/target/debug/simple")
make_fake_runtime(root + "/src/compiler_rust/target/release/simple")

val (stdout, stderr, code) = run_wrapper_with_simple_binary(
    root,
    root + "/src/compiler_rust/target/debug/simple",
    ["test", "test/unit/lib/common/simd_dispatch_facade_spec.spl"]
)

expect(code).to_equal(0)
expect(stderr).to_equal("")
expect_arg(stdout, 1, "test")
expect_arg(stdout, 2, "test/unit/lib/common/simd_dispatch_facade_spec.spl")
```

</details>

#### prefers the release runtime for the test path when SIMPLE_BINARY is unset

1. make fake runtime
2. make fake runtime
   - Expected: code equals `0`
   - Expected: stderr equals ``
3. expect arg
4. expect arg


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = setup_repo_root("test_path_release_default")
make_fake_runtime(root + "/src/compiler_rust/target/debug/simple")
make_fake_runtime(root + "/src/compiler_rust/target/release/simple")

val (stdout, stderr, code) = run_wrapper(root, ["test", "test/system/variant_api_parity_spec.spl"])

expect(code).to_equal(0)
expect(stderr).to_equal("")
expect(stdout).to_contain("argv0=" + root + "/src/compiler_rust/target/release/simple\n")
expect_arg(stdout, 1, "test")
expect_arg(stdout, 2, "test/system/variant_api_parity_spec.spl")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
