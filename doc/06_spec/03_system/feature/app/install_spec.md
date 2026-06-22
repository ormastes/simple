# Registry Install

> Feature coverage for the current `simple install` implementation. The command

<!-- sdn-diagram:id=install_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=install_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

install_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=install_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Registry Install

Feature coverage for the current `simple install` implementation. The command

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/app/install_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Feature coverage for the current `simple install` implementation. The command
installs dependencies declared in `simple.sdn`/`simple.toml` into a local
`simple_modules` directory, supports dry-run and JSON reporting, and can require
an existing lockfile in frozen mode.

## Scenarios

### Install from local manifest

#### when dependencies exist

#### reports dependency names in dry-run JSON

1.  setup manifest
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_manifest("name: install-fixture\nversion: 1.0.0\ndependencies:\n  alpha: \"*\"\n  beta: \"^2.0\"\ndev_dependencies:\n  gamma: \"3.1.4\"")

val (out, _err, code) = _run_install(["--dry-run", "--json"])

expect(code).to_equal(0)
expect(out).to_contain("\"dry_run\":true")
expect(out).to_contain("\"count\":3")
expect(out).to_contain("\"dependencies\":[\"alpha\",\"beta\",\"gamma\"]")
```

</details>

#### prints the dry-run install plan without creating modules

1.  setup manifest
   - Expected: code equals `0`
   - Expected: _path_exists("simple_modules") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_manifest("name: install-fixture\nversion: 1.0.0\ndependencies:\n  alpha: \"*\"\n  beta: \"*\"")

val (out, _err, code) = _run_install(["--dry-run", "--progress=none"])

expect(code).to_equal(0)
expect(out).to_contain("Would install 2 dependencies")
expect(out).to_contain("  alpha (*)")
expect(out).to_contain("  beta (*)")
expect(_path_exists("simple_modules")).to_equal(false)
```

</details>

#### creates package directories for manifest dependencies

1.  setup manifest
   - Expected: code equals `0`
   - Expected: _path_exists("simple_modules/alpha/__init__.spl") is true
   - Expected: _path_exists("simple_modules/beta/__init__.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_manifest("name: install-fixture\nversion: 1.0.0\ndependencies:\n  alpha: \"*\"\n  beta: \"*\"")

val (out, _err, code) = _run_install(["--progress=none"])

expect(code).to_equal(0)
expect(out).to_contain("Installing 2 dependencies")
expect(out).to_contain("Installed 2/2 packages to simple_modules/")
expect(_path_exists("simple_modules/alpha/__init__.spl")).to_equal(true)
expect(_path_exists("simple_modules/beta/__init__.spl")).to_equal(true)
```

</details>

#### writes installed module metadata

1.  setup manifest
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_manifest("name: install-fixture\nversion: 1.0.0\ndependencies:\n  alpha: \"*\"")

val (_out, _err, code) = _run_install(["--progress=none"])
val module_content = _read_fixture("simple_modules/alpha/__init__.spl")

expect(code).to_equal(0)
expect(module_content).to_contain("# alpha - installed by simple install")
expect(module_content).to_contain("# version: *")
```

</details>

#### generates a lockfile when one is missing

1.  setup manifest
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_manifest("name: install-fixture\nversion: 1.0.0\ndependencies:\n  alpha: \"*\"\ndev_dependencies:\n  gamma: \"*\"")

val (out, _err, code) = _run_install(["--progress=none"])
val lock_content = _read_fixture("simple.lock")

expect(code).to_equal(0)
expect(out).to_contain("Generated simple.lock")
expect(lock_content).to_contain("alpha: *")
expect(lock_content).to_contain("gamma: *")
```

</details>

#### when no manifest exists

#### shows an error message

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (_setup_out, _setup_err, _setup_code) = _shell("rm -rf " + FIXTURE_DIR + " && mkdir -p " + FIXTURE_DIR)

val (out, _err, code) = _run_install([])

expect(code).to_equal(1)
expect(out).to_contain("install: no simple.sdn or simple.toml found in current directory")
```

</details>

#### when no dependencies exist

#### reports zero dependencies in JSON

1.  setup manifest
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_manifest("name: install-fixture\nversion: 1.0.0")

val (out, _err, code) = _run_install(["--json"])

expect(code).to_equal(0)
expect(out).to_contain("\"count\":0")
expect(out).to_contain("\"dependencies\":[]")
```

</details>

#### prints a human no-op message

1.  setup manifest
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_manifest("name: install-fixture\nversion: 1.0.0")

val (out, _err, code) = _run_install([])

expect(code).to_equal(0)
expect(out).to_contain("No dependencies to install.")
```

</details>

#### when using --frozen

#### fails if simple.lock is missing

1.  setup manifest
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_manifest("name: install-fixture\nversion: 1.0.0\ndependencies:\n  alpha: \"*\"")

val (out, _err, code) = _run_install(["--frozen"])

expect(code).to_equal(1)
expect(out).to_contain("install: --frozen requires simple.lock to exist")
```

</details>

#### installs from the manifest when simple.lock exists

1.  setup manifest
   - Expected: code equals `0`
   - Expected: out does not contain `Generated simple.lock`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_manifest("name: install-fixture\nversion: 1.0.0\ndependencies:\n  alpha: \"*\"")
val (_lock_out, _lock_err, _lock_code) = _shell("cat > " + FIXTURE_DIR + "/simple.lock <<'EOF'\nalpha: *\nEOF")

val (out, _err, code) = _run_install(["--frozen", "--progress=none"])

expect(code).to_equal(0)
expect(out).to_contain("Installed 1/1 packages to simple_modules/")
expect(out.contains("Generated simple.lock")).to_equal(false)
```

</details>

### Install dependency selection

#### includes dependencies and dev dependencies in manifest order

1.  setup manifest
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_setup_manifest("name: install-fixture\nversion: 1.0.0\ndependencies:\n  alpha: \"^1.0\"\n  beta: \"2.0.0\"\ndev_dependencies:\n  gamma: \"*\"")

val (out, _err, code) = _run_install(["--dry-run", "--json"])

expect(code).to_equal(0)
expect(out).to_contain("\"dependencies\":[\"alpha\",\"beta\",\"gamma\"]")
```

</details>

#### accepts simple.toml when simple.sdn is absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (_setup_out, _setup_err, _setup_code) = _shell(
    "rm -rf " + FIXTURE_DIR + " && mkdir -p " + FIXTURE_DIR + " && cat > " + FIXTURE_DIR + "/simple.toml <<'EOF'\nname: install-fixture\nversion: 1.0.0\ndependencies:\n  alpha: \"*\"\nEOF"
)

val (out, _err, code) = _run_install(["--dry-run", "--json"])

expect(code).to_equal(0)
expect(out).to_contain("\"dependencies\":[\"alpha\"]")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
