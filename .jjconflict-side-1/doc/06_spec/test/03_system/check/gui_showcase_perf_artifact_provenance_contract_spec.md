# GUI Showcase Perf Artifact Provenance Contract

> Validates that retained 4K/8K GUI showcase performance completion evidence is bound to regular artifact files. The GUI RenderDoc aggregate must not accept symlinked or hardlinked showcase logs, time logs, alias sources, native binaries, or native build logs as completion proof.

<!-- sdn-diagram:id=gui_showcase_perf_artifact_provenance_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_showcase_perf_artifact_provenance_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_showcase_perf_artifact_provenance_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_showcase_perf_artifact_provenance_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI Showcase Perf Artifact Provenance Contract

Validates that retained 4K/8K GUI showcase performance completion evidence is bound to regular artifact files. The GUI RenderDoc aggregate must not accept symlinked or hardlinked showcase logs, time logs, alias sources, native binaries, or native build logs as completion proof.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/gui_showcase_perf_artifact_provenance_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that retained 4K/8K GUI showcase performance completion evidence is
bound to regular artifact files. The GUI RenderDoc aggregate must not accept
symlinked or hardlinked showcase logs, time logs, alias sources, native
binaries, or native build logs as completion proof.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
bin/simple test test/03_system/check/gui_showcase_perf_artifact_provenance_contract_spec.spl --mode=interpreter
```

## Acceptance

- A complete retained 4K performance row with a symlinked time log fails with a
  typed `time_log=symlink` reason.
- A complete retained 8K performance row with a symlinked native binary fails
  with typed `native_bin=symlink` and executable `symlink` rows.
- The aggregate implementation uses regular-file checks for showcase
  performance artifact paths and does not read native binary magic through
  symlinks.
- The retained perf producer prefers release/self-hosted binaries before
  repo-bin shims so native perf evidence does not depend on a slower or stale
  launcher.
- Complete retained showcase rows must include `*_simple_bin_status=pass`; the
  aggregate must not infer binary validity from path/source text alone.
- Complete retained showcase rows must not use the Rust seed binary as
  `*_simple_bin`; 4K/8K completion requires self-hosted Simple evidence.
- Complete retained showcase rows must come from `*_simple_bin_source=
  self-hosted-release`; repo launcher shims are routing fallbacks, not retained
  perf completion proof.
- Complete retained showcase rows must also point `*_simple_bin` at a release
  self-hosted path; a forged source label on `bin/simple` must fail.
- Hardlinked retained logs or native binaries fail with typed `hardlink`
  artifact status so reused artifacts cannot masquerade as fresh evidence.
- Complete retained showcase rows must include every source file used by the
  current 4K/8K digest so stale two-file rows cannot satisfy completion gates.

## Evidence Contract

The aggregate consumes retained showcase producer rows from
`GUI_SHOWCASE_4K_PERF_ENV` and `GUI_SHOWCASE_8K_PERF_ENV`. A retained
completion row must point at the concrete files used for measurement:

- `*_log`
- `*_time_log`
- `*_alias_src`
- `*_native_bin`
- `*_native_build_log`

The aggregate recomputes the file state for those paths. Producer-side
`*_file_status=pass` claims are advisory only; they cannot override the current
filesystem state. A path is accepted only when it is a regular, non-symlink,
non-hardlink file. Native binaries also need executable permission and a
recognized ELF, Mach-O, or PE header before 4K/8K retained performance can
count as native evidence.

## Failure Semantics

The aggregate emits typed file states into the normalized
`gui_showcase_4k_200fps_*` and `gui_showcase_8k_perf_*` rows:

- `pass`: the current artifact is a local regular file.
- `missing`: the artifact path is absent or not a regular file.
- `symlink`: the artifact path is a symbolic link and cannot prove local
  retained measurement.
- `hardlink`: the artifact has multiple directory entries and may be reused
  evidence from another lane.

These states are included in the final failure reason, for example
`log=hardlink`, `time_log=symlink`, or `native_bin=hardlink`. Reviewers should
fix the producer path and rerun the retained showcase wrapper rather than
editing the env file.

## Operator Flow

1. Run the retained wrapper in plan-only mode when checking routing:
   `PLAN_ONLY=1 RESOLUTION=4k scripts/check/check-widget-showcase-4k-200fps.shs`.
2. Run the real retained 4K or 8K wrapper on a host that can build and execute
   the native alias binary.
3. Feed the resulting status env into
   `scripts/check/check-gui-renderdoc-feature-coverage-status.shs`.
4. Inspect the normalized artifact statuses in the aggregate evidence. A
   `pass` producer row downgraded to `fail` means the referenced files are not
   acceptable completion proof.

## Test Matrix

1. Reject symlinked 4K retained logs and symlinked 8K native binaries.
2. Assert the aggregate implementation uses regular-file and
   regular-executable checks for retained showcase artifact paths.
3. Assert the producer prefers release/self-hosted binaries before repo
   launcher shims.
4. Reject complete-looking rows that omit `*_simple_bin_status`.
5. Reject complete-looking rows that point `*_simple_bin` at the Rust seed.
6. Reject complete-looking rows whose Simple binary source is `repo-bin`.
7. Reject hardlinked 4K retained logs and hardlinked 8K native binaries.
8. Reject forged `self-hosted-release` labels on `bin/simple`.
9. Reject complete-looking 4K/8K rows with truncated source revision file sets.

## Completion Boundary

This spec does not prove the host can hit 4K or 8K at 200 FPS. It proves that
when a retained performance row claims that result, the aggregate does not
accept substituted artifact paths as evidence. Real completion still requires
fresh native retained measurements with resolution, FPS, frame timing, RSS,
checksum/readback, retained redraw, source revision, and native binary
provenance all passing.

## Scenarios

### GUI showcase perf artifact provenance contract

#### rejects symlinked retained showcase artifact paths

- "printf 'fn main
   - Expected: code equals `0`
- Confirm symlinked 4K retained logs cannot satisfy perf completion
   - Expected: _value_of(four_k, "gui_showcase_4k_200fps_status") equals `fail`
   - Expected: _value_of(four_k, "gui_showcase_4k_200fps_log_file_status") equals `symlink`
   - Expected: _value_of(four_k, "gui_showcase_4k_200fps_time_log_file_status") equals `symlink`
   - Expected: _value_of(four_k, "gui_showcase_4k_200fps_reason") equals `missing-4k-retained-log-artifacts:log=symlink;time_log=symlink`
- Confirm symlinked 8K native binaries cannot satisfy native provenance
   - Expected: _value_of(eight_k, "gui_showcase_8k_perf_status") equals `fail`
   - Expected: _value_of(eight_k, "gui_showcase_8k_perf_native_bin_file_status") equals `symlink`
   - Expected: _value_of(eight_k, "gui_showcase_8k_perf_native_bin_executable_status") equals `symlink`
   - Expected: _value_of(eight_k, "gui_showcase_8k_perf_native_bin_magic") equals ``
   - Expected: _value_of(eight_k, "gui_showcase_8k_perf_native_bin_format_status") equals `fail`
   - Expected: _value_of(eight_k, "gui_showcase_8k_perf_reason") equals `missing-8k-native-artifacts:alias_src=pass;native_bin=symlink;native_bin_exec... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-gui-showcase-perf-artifact-provenance"
val setup = "rm -rf " + root + " && mkdir -p " + root + "/4k " + root + "/8k && " +
    "printf '%b' '\\177ELFsynthetic-native\\n' > " + root + "/4k/native-real.bin && chmod +x " + root + "/4k/native-real.bin && " +
    "printf '%b' '\\177ELFsynthetic-native\\n' > " + root + "/8k/native-real.bin && chmod +x " + root + "/8k/native-real.bin && ln -s native-real.bin " + root + "/8k/native-link.bin && " +
    "printf 'fn main() -> i64:\\n    0\\n' > " + root + "/4k/showcase.spl && printf 'fn main() -> i64:\\n    0\\n' > " + root + "/8k/showcase.spl && " +
    "printf 'native build log\\n' > " + root + "/4k/build.log && printf 'native build log\\n' > " + root + "/8k/build.log && " +
    "printf 'showcase retained log\\n' > " + root + "/4k/showcase-real.log && ln -s showcase-real.log " + root + "/4k/showcase.log && " +
    "printf 'elapsed_ms=597\\n' > " + root + "/4k/time-real.log && ln -s time-real.log " + root + "/4k/time.log && " +
    "printf 'showcase retained log\\n' > " + root + "/8k/showcase.log && printf 'elapsed_ms=597\\n' > " + root + "/8k/time.log && "
val write_4k = _fixture_command(root, "4k", root + "/4k/native-real.bin", root + "/4k/showcase.spl", root + "/4k/build.log", root + "/4k/showcase.log", root + "/4k/time.log")
val write_8k = _fixture_command(root, "8k", root + "/8k/native-link.bin", root + "/8k/showcase.spl", root + "/8k/build.log", root + "/8k/showcase.log", root + "/8k/time.log")
val command = setup + write_4k + " && " + write_8k + " && " +
    "GUI_SHOWCASE_4K_PERF_ENV=" + root + "/4k/status.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=" + root + "/out-4k REPORT_PATH=" + root + "/report-4k.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs && " +
    "GUI_SHOWCASE_8K_PERF_ENV=" + root + "/8k/status.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=" + root + "/out-8k REPORT_PATH=" + root + "/report-8k.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val four_k = file_read(root + "/out-4k/evidence.env")
val eight_k = file_read(root + "/out-8k/evidence.env")
step("Confirm symlinked 4K retained logs cannot satisfy perf completion")
expect(_value_of(four_k, "gui_showcase_4k_200fps_status")).to_equal("fail")
expect(_value_of(four_k, "gui_showcase_4k_200fps_log_file_status")).to_equal("symlink")
expect(_value_of(four_k, "gui_showcase_4k_200fps_time_log_file_status")).to_equal("symlink")
expect(_value_of(four_k, "gui_showcase_4k_200fps_reason")).to_equal("missing-4k-retained-log-artifacts:log=symlink;time_log=symlink")

step("Confirm symlinked 8K native binaries cannot satisfy native provenance")
expect(_value_of(eight_k, "gui_showcase_8k_perf_status")).to_equal("fail")
expect(_value_of(eight_k, "gui_showcase_8k_perf_native_bin_file_status")).to_equal("symlink")
expect(_value_of(eight_k, "gui_showcase_8k_perf_native_bin_executable_status")).to_equal("symlink")
expect(_value_of(eight_k, "gui_showcase_8k_perf_native_bin_magic")).to_equal("")
expect(_value_of(eight_k, "gui_showcase_8k_perf_native_bin_format_status")).to_equal("fail")
expect(_value_of(eight_k, "gui_showcase_8k_perf_reason")).to_equal("missing-8k-native-artifacts:alias_src=pass;native_bin=symlink;native_bin_executable=symlink;native_bin_format=fail;native_build_log=pass")
```

</details>

#### keeps the aggregate wired to regular showcase artifact checks

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-gui-renderdoc-feature-coverage-status.shs")
expect(script).to_contain("def regular_file_status")
expect(script).to_contain("path.is_symlink()")
expect(script).to_contain("path.stat().st_nlink > 1")
expect(script).to_contain("def evidence_regular_file_status")
expect(script).to_contain("def evidence_regular_executable_status")
expect(script).to_contain("showcase_4k_log_file_status = regular_file_status(showcase_4k_log)")
expect(script).to_contain("showcase_8k_time_log_file_status = regular_file_status(showcase_8k_time_log)")
expect(script).to_contain("showcase_4k_native_bin_file_status = evidence_regular_file_status")
expect(script).to_contain("showcase_8k_native_bin_executable_status = evidence_regular_executable_status")
expect(script).to_contain("showcase_4k_simple_bin_status = value_of")
expect(script).to_contain("showcase_8k_simple_bin_status = value_of")
expect(script).to_contain("simple_bin_status=<missing>")
expect(script).to_contain("simple_bin_status=\" + simple_bin_status")
```

</details>

#### prefers release self-hosted binaries before repo-bin shims for retained perf producer evidence

- Assert default discovery tries release/self-hosted binaries before bin/simple
- Assert release paths are labelled as self-hosted perf evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-widget-showcase-4k-200fps.shs")
step("Assert default discovery tries release/self-hosted binaries before bin/simple")
expect(script).to_contain("for candidate in \\\n        release/x86_64-unknown-linux-gnu/simple")
expect(script).to_contain("bin/release/x86_64-apple-darwin/simple \\\n        bin/simple")

step("Assert release paths are labelled as self-hosted perf evidence")
expect(script).to_contain("release/*|bin/release/*) SIMPLE_BIN_SOURCE=\"self-hosted-release\"")
expect(script).to_contain("*) SIMPLE_BIN_SOURCE=\"repo-bin\"")
expect(script).to_contain("SIMPLE_BIN_STATUS=\"${SIMPLE_BIN_STATUS:-pass}\"")
expect(script).to_contain("_simple_bin_status=$SIMPLE_BIN_STATUS")
```

</details>

#### rejects complete retained rows missing simple binary status

- "printf 'fn main
   - Expected: code equals `0`
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_status") equals `fail`
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_reason") equals `missing-4k-perf-provenance:simple_bin_status`
   - Expected: _value_of(evidence, "gui_showcase_4k_200fps_simple_bin_status") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-gui-showcase-perf-simple-bin-status"
val setup = "rm -rf " + root + " && mkdir -p " + root + "/4k && " +
    "printf '%b' '\\177ELFsynthetic-native\\n' > " + root + "/4k/native.bin && chmod +x " + root + "/4k/native.bin && " +
    "printf 'fn main() -> i64:\\n    0\\n' > " + root + "/4k/showcase.spl && " +
    "printf 'native build log\\n' > " + root + "/4k/build.log && " +
    "printf 'showcase retained log\\n' > " + root + "/4k/showcase.log && " +
    "printf 'elapsed_ms=597\\n' > " + root + "/4k/time.log && "
val write_4k = _fixture_command(root, "4k", root + "/4k/native.bin", root + "/4k/showcase.spl", root + "/4k/build.log", root + "/4k/showcase.log", root + "/4k/time.log")
val command = setup + write_4k + " && sed -i '/gui_showcase_4k_200fps_simple_bin_status=/d' " + root + "/4k/status.env && " +
    "GUI_SHOWCASE_4K_PERF_ENV=" + root + "/4k/status.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(_value_of(evidence, "gui_showcase_4k_200fps_status")).to_equal("fail")
expect(_value_of(evidence, "gui_showcase_4k_200fps_reason")).to_equal("missing-4k-perf-provenance:simple_bin_status")
expect(_value_of(evidence, "gui_showcase_4k_200fps_simple_bin_status")).to_equal("")
```

</details>

#### rejects retained rows using the Rust seed as the Simple binary

- "printf 'fn main
   - Expected: code equals `0`
- Reject Rust seed provenance for 4K retained completion
   - Expected: _value_of(four_k, "gui_showcase_4k_200fps_status") equals `fail`
   - Expected: _value_of(four_k, "gui_showcase_4k_200fps_simple_bin") equals `rust_seed`
   - Expected: _value_of(four_k, "gui_showcase_4k_200fps_reason") equals `invalid-4k-simple-bin-provenance:simple_bin=rust-seed-forbidden`
- Reject Rust seed provenance for 8K retained completion
   - Expected: _value_of(eight_k, "gui_showcase_8k_perf_status") equals `fail`
   - Expected: _value_of(eight_k, "gui_showcase_8k_perf_simple_bin") equals `rust_seed`
   - Expected: _value_of(eight_k, "gui_showcase_8k_perf_reason") equals `invalid-8k-simple-bin-provenance:simple_bin=rust-seed-forbidden`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-gui-showcase-perf-rust-seed-provenance"
val setup = "rm -rf " + root + " && mkdir -p " + root + "/4k " + root + "/8k && " +
    "printf '%b' '\\177ELFsynthetic-native\\n' > " + root + "/4k/native.bin && chmod +x " + root + "/4k/native.bin && " +
    "printf '%b' '\\177ELFsynthetic-native\\n' > " + root + "/8k/native.bin && chmod +x " + root + "/8k/native.bin && " +
    "printf 'fn main() -> i64:\\n    0\\n' > " + root + "/4k/showcase.spl && printf 'fn main() -> i64:\\n    0\\n' > " + root + "/8k/showcase.spl && " +
    "printf 'native build log\\n' > " + root + "/4k/build.log && printf 'native build log\\n' > " + root + "/8k/build.log && " +
    "printf 'showcase retained log\\n' > " + root + "/4k/showcase.log && printf 'showcase retained log\\n' > " + root + "/8k/showcase.log && " +
    "printf 'elapsed_ms=597\\n' > " + root + "/4k/time.log && printf 'elapsed_ms=597\\n' > " + root + "/8k/time.log && "
val write_4k = _fixture_command(root, "4k", root + "/4k/native.bin", root + "/4k/showcase.spl", root + "/4k/build.log", root + "/4k/showcase.log", root + "/4k/time.log")
val write_8k = _fixture_command(root, "8k", root + "/8k/native.bin", root + "/8k/showcase.spl", root + "/8k/build.log", root + "/8k/showcase.log", root + "/8k/time.log")
val rust_seed = "src/compiler_rust/target/release/simple"
val command = setup + write_4k + " && " + write_8k + " && " +
    "sed -i 's#gui_showcase_4k_200fps_simple_bin=bin/release/x86_64-unknown-linux-gnu/simple#gui_showcase_4k_200fps_simple_bin=" + rust_seed + "#' " + root + "/4k/status.env && " +
    "sed -i 's#gui_showcase_8k_perf_simple_bin=bin/release/x86_64-unknown-linux-gnu/simple#gui_showcase_8k_perf_simple_bin=" + rust_seed + "#' " + root + "/8k/status.env && " +
    "GUI_SHOWCASE_4K_PERF_ENV=" + root + "/4k/status.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=" + root + "/out-4k REPORT_PATH=" + root + "/report-4k.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs && " +
    "GUI_SHOWCASE_8K_PERF_ENV=" + root + "/8k/status.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=" + root + "/out-8k REPORT_PATH=" + root + "/report-8k.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val four_k = file_read(root + "/out-4k/evidence.env")
val eight_k = file_read(root + "/out-8k/evidence.env")
step("Reject Rust seed provenance for 4K retained completion")
expect(_value_of(four_k, "gui_showcase_4k_200fps_status")).to_equal("fail")
expect(_value_of(four_k, "gui_showcase_4k_200fps_simple_bin")).to_equal(rust_seed)
expect(_value_of(four_k, "gui_showcase_4k_200fps_reason")).to_equal("invalid-4k-simple-bin-provenance:simple_bin=rust-seed-forbidden")

step("Reject Rust seed provenance for 8K retained completion")
expect(_value_of(eight_k, "gui_showcase_8k_perf_status")).to_equal("fail")
expect(_value_of(eight_k, "gui_showcase_8k_perf_simple_bin")).to_equal(rust_seed)
expect(_value_of(eight_k, "gui_showcase_8k_perf_reason")).to_equal("invalid-8k-simple-bin-provenance:simple_bin=rust-seed-forbidden")
```

</details>

#### rejects retained rows using repo-bin launcher provenance

- "printf 'fn main
   - Expected: code equals `0`
- Reject repo-bin provenance for 4K retained completion
   - Expected: _value_of(four_k, "gui_showcase_4k_200fps_status") equals `fail`
   - Expected: _value_of(four_k, "gui_showcase_4k_200fps_simple_bin_source") equals `repo-bin`
   - Expected: _value_of(four_k, "gui_showcase_4k_200fps_reason") equals `invalid-4k-simple-bin-provenance:simple_bin_source=repo-bin`
- Reject repo-bin provenance for 8K retained completion
   - Expected: _value_of(eight_k, "gui_showcase_8k_perf_status") equals `fail`
   - Expected: _value_of(eight_k, "gui_showcase_8k_perf_simple_bin_source") equals `repo-bin`
   - Expected: _value_of(eight_k, "gui_showcase_8k_perf_reason") equals `invalid-8k-simple-bin-provenance:simple_bin_source=repo-bin`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-gui-showcase-perf-repo-bin-provenance"
val setup = "rm -rf " + root + " && mkdir -p " + root + "/4k " + root + "/8k && " +
    "printf '%b' '\\177ELFsynthetic-native\\n' > " + root + "/4k/native.bin && chmod +x " + root + "/4k/native.bin && " +
    "printf '%b' '\\177ELFsynthetic-native\\n' > " + root + "/8k/native.bin && chmod +x " + root + "/8k/native.bin && " +
    "printf 'fn main() -> i64:\\n    0\\n' > " + root + "/4k/showcase.spl && printf 'fn main() -> i64:\\n    0\\n' > " + root + "/8k/showcase.spl && " +
    "printf 'native build log\\n' > " + root + "/4k/build.log && printf 'native build log\\n' > " + root + "/8k/build.log && " +
    "printf 'showcase retained log\\n' > " + root + "/4k/showcase.log && printf 'showcase retained log\\n' > " + root + "/8k/showcase.log && " +
    "printf 'elapsed_ms=597\\n' > " + root + "/4k/time.log && printf 'elapsed_ms=597\\n' > " + root + "/8k/time.log && "
val write_4k = _fixture_command(root, "4k", root + "/4k/native.bin", root + "/4k/showcase.spl", root + "/4k/build.log", root + "/4k/showcase.log", root + "/4k/time.log")
val write_8k = _fixture_command(root, "8k", root + "/8k/native.bin", root + "/8k/showcase.spl", root + "/8k/build.log", root + "/8k/showcase.log", root + "/8k/time.log")
val command = setup + write_4k + " && " + write_8k + " && " +
    "sed -i 's#simple_bin_source=self-hosted-release#simple_bin_source=repo-bin#' " + root + "/4k/status.env && " +
    "sed -i 's#simple_bin_source=self-hosted-release#simple_bin_source=repo-bin#' " + root + "/8k/status.env && " +
    "GUI_SHOWCASE_4K_PERF_ENV=" + root + "/4k/status.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=" + root + "/out-4k REPORT_PATH=" + root + "/report-4k.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs && " +
    "GUI_SHOWCASE_8K_PERF_ENV=" + root + "/8k/status.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=" + root + "/out-8k REPORT_PATH=" + root + "/report-8k.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val four_k = file_read(root + "/out-4k/evidence.env")
val eight_k = file_read(root + "/out-8k/evidence.env")
step("Reject repo-bin provenance for 4K retained completion")
expect(_value_of(four_k, "gui_showcase_4k_200fps_status")).to_equal("fail")
expect(_value_of(four_k, "gui_showcase_4k_200fps_simple_bin_source")).to_equal("repo-bin")
expect(_value_of(four_k, "gui_showcase_4k_200fps_reason")).to_equal("invalid-4k-simple-bin-provenance:simple_bin_source=repo-bin")

step("Reject repo-bin provenance for 8K retained completion")
expect(_value_of(eight_k, "gui_showcase_8k_perf_status")).to_equal("fail")
expect(_value_of(eight_k, "gui_showcase_8k_perf_simple_bin_source")).to_equal("repo-bin")
expect(_value_of(eight_k, "gui_showcase_8k_perf_reason")).to_equal("invalid-8k-simple-bin-provenance:simple_bin_source=repo-bin")
```

</details>

#### rejects forged release source labels on repo launcher paths

- "printf 'fn main
   - Expected: code equals `0`
- Reject forged release provenance for 4K retained completion
   - Expected: _value_of(four_k, "gui_showcase_4k_200fps_status") equals `fail`
   - Expected: _value_of(four_k, "gui_showcase_4k_200fps_simple_bin") equals `bin/simple`
   - Expected: _value_of(four_k, "gui_showcase_4k_200fps_reason") equals `invalid-4k-simple-bin-provenance:simple_bin=not-release-self-hosted`
- Reject forged release provenance for 8K retained completion
   - Expected: _value_of(eight_k, "gui_showcase_8k_perf_status") equals `fail`
   - Expected: _value_of(eight_k, "gui_showcase_8k_perf_simple_bin") equals `bin/simple`
   - Expected: _value_of(eight_k, "gui_showcase_8k_perf_reason") equals `invalid-8k-simple-bin-provenance:simple_bin=not-release-self-hosted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-gui-showcase-perf-forged-release-provenance"
val setup = "rm -rf " + root + " && mkdir -p " + root + "/4k " + root + "/8k && " +
    "printf '%b' '\\177ELFsynthetic-native\\n' > " + root + "/4k/native.bin && chmod +x " + root + "/4k/native.bin && " +
    "printf '%b' '\\177ELFsynthetic-native\\n' > " + root + "/8k/native.bin && chmod +x " + root + "/8k/native.bin && " +
    "printf 'fn main() -> i64:\\n    0\\n' > " + root + "/4k/showcase.spl && printf 'fn main() -> i64:\\n    0\\n' > " + root + "/8k/showcase.spl && " +
    "printf 'native build log\\n' > " + root + "/4k/build.log && printf 'native build log\\n' > " + root + "/8k/build.log && " +
    "printf 'showcase retained log\\n' > " + root + "/4k/showcase.log && printf 'showcase retained log\\n' > " + root + "/8k/showcase.log && " +
    "printf 'elapsed_ms=597\\n' > " + root + "/4k/time.log && printf 'elapsed_ms=597\\n' > " + root + "/8k/time.log && "
val write_4k = _fixture_command(root, "4k", root + "/4k/native.bin", root + "/4k/showcase.spl", root + "/4k/build.log", root + "/4k/showcase.log", root + "/4k/time.log")
val write_8k = _fixture_command(root, "8k", root + "/8k/native.bin", root + "/8k/showcase.spl", root + "/8k/build.log", root + "/8k/showcase.log", root + "/8k/time.log")
val command = setup + write_4k + " && " + write_8k + " && " +
    "sed -i 's#simple_bin=bin/release/x86_64-unknown-linux-gnu/simple#simple_bin=bin/simple#' " + root + "/4k/status.env && " +
    "sed -i 's#simple_bin=bin/release/x86_64-unknown-linux-gnu/simple#simple_bin=bin/simple#' " + root + "/8k/status.env && " +
    "GUI_SHOWCASE_4K_PERF_ENV=" + root + "/4k/status.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=" + root + "/out-4k REPORT_PATH=" + root + "/report-4k.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs && " +
    "GUI_SHOWCASE_8K_PERF_ENV=" + root + "/8k/status.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=" + root + "/out-8k REPORT_PATH=" + root + "/report-8k.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val four_k = file_read(root + "/out-4k/evidence.env")
val eight_k = file_read(root + "/out-8k/evidence.env")
step("Reject forged release provenance for 4K retained completion")
expect(_value_of(four_k, "gui_showcase_4k_200fps_status")).to_equal("fail")
expect(_value_of(four_k, "gui_showcase_4k_200fps_simple_bin")).to_equal("bin/simple")
expect(_value_of(four_k, "gui_showcase_4k_200fps_reason")).to_equal("invalid-4k-simple-bin-provenance:simple_bin=not-release-self-hosted")

step("Reject forged release provenance for 8K retained completion")
expect(_value_of(eight_k, "gui_showcase_8k_perf_status")).to_equal("fail")
expect(_value_of(eight_k, "gui_showcase_8k_perf_simple_bin")).to_equal("bin/simple")
expect(_value_of(eight_k, "gui_showcase_8k_perf_reason")).to_equal("invalid-8k-simple-bin-provenance:simple_bin=not-release-self-hosted")
```

</details>

#### rejects retained rows with truncated source revision file sets

- "printf 'fn main
   - Expected: code equals `0`
- Reject a complete-looking 4K row that only lists the old two source files
   - Expected: _value_of(four_k, "gui_showcase_4k_200fps_status") equals `fail`
   - Expected: _value_of(four_k, "gui_showcase_4k_200fps_source_revision_files_status") equals `fail`
   - Expected: _value_of(four_k, "gui_showcase_4k_200fps_missing_source_revision_files") equals `missing`
   - Expected: _value_of(four_k, "gui_showcase_4k_200fps_reason") equals `"missing-4k-source-revision-files:" + missing`
- Reject a complete-looking 8K row that only lists the old two source files
   - Expected: _value_of(eight_k, "gui_showcase_8k_perf_status") equals `fail`
   - Expected: _value_of(eight_k, "gui_showcase_8k_perf_source_revision_files_status") equals `fail`
   - Expected: _value_of(eight_k, "gui_showcase_8k_perf_missing_source_revision_files") equals `missing`
   - Expected: _value_of(eight_k, "gui_showcase_8k_perf_reason") equals `"missing-8k-source-revision-files:" + missing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-gui-showcase-perf-source-revision-files"
val setup = "rm -rf " + root + " && mkdir -p " + root + "/4k " + root + "/8k && " +
    "printf '%b' '\\177ELFsynthetic-native\\n' > " + root + "/4k/native.bin && chmod +x " + root + "/4k/native.bin && " +
    "printf '%b' '\\177ELFsynthetic-native\\n' > " + root + "/8k/native.bin && chmod +x " + root + "/8k/native.bin && " +
    "printf 'fn main() -> i64:\\n    0\\n' > " + root + "/4k/showcase.spl && printf 'fn main() -> i64:\\n    0\\n' > " + root + "/8k/showcase.spl && " +
    "printf 'native build log\\n' > " + root + "/4k/build.log && printf 'native build log\\n' > " + root + "/8k/build.log && " +
    "printf 'showcase retained log\\n' > " + root + "/4k/showcase.log && printf 'showcase retained log\\n' > " + root + "/8k/showcase.log && " +
    "printf 'elapsed_ms=597\\n' > " + root + "/4k/time.log && printf 'elapsed_ms=597\\n' > " + root + "/8k/time.log && "
val write_4k = _fixture_command(root, "4k", root + "/4k/native.bin", root + "/4k/showcase.spl", root + "/4k/build.log", root + "/4k/showcase.log", root + "/4k/time.log")
val write_8k = _fixture_command(root, "8k", root + "/8k/native.bin", root + "/8k/showcase.spl", root + "/8k/build.log", root + "/8k/showcase.log", root + "/8k/time.log")
val remove_suffix = "sed -i 's# examples/06_io/ui/showcase_8k_scroll_gui.spl src/lib/common/ui/scroll_surface.spl src/lib/common/ui/dirty_region.spl src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl##'"
val command = setup + write_4k + " && " + write_8k + " && " +
    remove_suffix + " " + root + "/4k/status.env && " +
    remove_suffix + " " + root + "/8k/status.env && " +
    "GUI_SHOWCASE_4K_PERF_ENV=" + root + "/4k/status.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=" + root + "/out-4k REPORT_PATH=" + root + "/report-4k.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs && " +
    "GUI_SHOWCASE_8K_PERF_ENV=" + root + "/8k/status.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=" + root + "/out-8k REPORT_PATH=" + root + "/report-8k.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val four_k = file_read(root + "/out-4k/evidence.env")
val eight_k = file_read(root + "/out-8k/evidence.env")
val missing = "examples/06_io/ui/showcase_8k_scroll_gui.spl,src/lib/common/ui/scroll_surface.spl,src/lib/common/ui/dirty_region.spl,src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl"
step("Reject a complete-looking 4K row that only lists the old two source files")
expect(_value_of(four_k, "gui_showcase_4k_200fps_status")).to_equal("fail")
expect(_value_of(four_k, "gui_showcase_4k_200fps_source_revision_files_status")).to_equal("fail")
expect(_value_of(four_k, "gui_showcase_4k_200fps_missing_source_revision_files")).to_equal(missing)
expect(_value_of(four_k, "gui_showcase_4k_200fps_reason")).to_equal("missing-4k-source-revision-files:" + missing)

step("Reject a complete-looking 8K row that only lists the old two source files")
expect(_value_of(eight_k, "gui_showcase_8k_perf_status")).to_equal("fail")
expect(_value_of(eight_k, "gui_showcase_8k_perf_source_revision_files_status")).to_equal("fail")
expect(_value_of(eight_k, "gui_showcase_8k_perf_missing_source_revision_files")).to_equal(missing)
expect(_value_of(eight_k, "gui_showcase_8k_perf_reason")).to_equal("missing-8k-source-revision-files:" + missing)
```

</details>

#### rejects hardlinked retained showcase artifact paths

- "printf 'fn main
   - Expected: code equals `0`
   - Expected: _value_of(four_k, "gui_showcase_4k_200fps_status") equals `fail`
   - Expected: _value_of(four_k, "gui_showcase_4k_200fps_log_file_status") equals `hardlink`
   - Expected: _value_of(four_k, "gui_showcase_4k_200fps_time_log_file_status") equals `hardlink`
   - Expected: _value_of(four_k, "gui_showcase_4k_200fps_reason") equals `missing-4k-retained-log-artifacts:log=hardlink;time_log=hardlink`
   - Expected: _value_of(eight_k, "gui_showcase_8k_perf_status") equals `fail`
   - Expected: _value_of(eight_k, "gui_showcase_8k_perf_native_bin_file_status") equals `hardlink`
   - Expected: _value_of(eight_k, "gui_showcase_8k_perf_native_bin_executable_status") equals `hardlink`
   - Expected: _value_of(eight_k, "gui_showcase_8k_perf_reason") equals `missing-8k-native-artifacts:alias_src=pass;native_bin=hardlink;native_bin_exe... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-gui-showcase-perf-artifact-hardlink"
val setup = "rm -rf " + root + " && mkdir -p " + root + "/4k " + root + "/8k && " +
    "printf '%b' '\\177ELFsynthetic-native\\n' > " + root + "/4k/native.bin && chmod +x " + root + "/4k/native.bin && " +
    "printf '%b' '\\177ELFsynthetic-native\\n' > " + root + "/8k/native-original.bin && chmod +x " + root + "/8k/native-original.bin && ln " + root + "/8k/native-original.bin " + root + "/8k/native-hardlink.bin && " +
    "printf 'fn main() -> i64:\\n    0\\n' > " + root + "/4k/showcase.spl && printf 'fn main() -> i64:\\n    0\\n' > " + root + "/8k/showcase.spl && " +
    "printf 'native build log\\n' > " + root + "/4k/build.log && printf 'native build log\\n' > " + root + "/8k/build.log && " +
    "printf 'showcase retained log\\n' > " + root + "/4k/showcase-real.log && ln " + root + "/4k/showcase-real.log " + root + "/4k/showcase-hardlink.log && " +
    "printf 'elapsed_ms=597\\n' > " + root + "/4k/time-real.log && ln " + root + "/4k/time-real.log " + root + "/4k/time-hardlink.log && " +
    "printf 'showcase retained log\\n' > " + root + "/8k/showcase.log && printf 'elapsed_ms=597\\n' > " + root + "/8k/time.log && "
val write_4k = _fixture_command(root, "4k", root + "/4k/native.bin", root + "/4k/showcase.spl", root + "/4k/build.log", root + "/4k/showcase-hardlink.log", root + "/4k/time-hardlink.log")
val write_8k = _fixture_command(root, "8k", root + "/8k/native-hardlink.bin", root + "/8k/showcase.spl", root + "/8k/build.log", root + "/8k/showcase.log", root + "/8k/time.log")
val command = setup + write_4k + " && " + write_8k + " && " +
    "GUI_SHOWCASE_4K_PERF_ENV=" + root + "/4k/status.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=" + root + "/out-4k REPORT_PATH=" + root + "/report-4k.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs && " +
    "GUI_SHOWCASE_8K_PERF_ENV=" + root + "/8k/status.env GUI_RENDERDOC_AGGREGATE_STATIC_CACHE_DIR=build/test-gui-renderdoc-feature-coverage-static-cache BUILD_DIR=" + root + "/out-8k REPORT_PATH=" + root + "/report-8k.md sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val four_k = file_read(root + "/out-4k/evidence.env")
val eight_k = file_read(root + "/out-8k/evidence.env")
expect(_value_of(four_k, "gui_showcase_4k_200fps_status")).to_equal("fail")
expect(_value_of(four_k, "gui_showcase_4k_200fps_log_file_status")).to_equal("hardlink")
expect(_value_of(four_k, "gui_showcase_4k_200fps_time_log_file_status")).to_equal("hardlink")
expect(_value_of(four_k, "gui_showcase_4k_200fps_reason")).to_equal("missing-4k-retained-log-artifacts:log=hardlink;time_log=hardlink")

expect(_value_of(eight_k, "gui_showcase_8k_perf_status")).to_equal("fail")
expect(_value_of(eight_k, "gui_showcase_8k_perf_native_bin_file_status")).to_equal("hardlink")
expect(_value_of(eight_k, "gui_showcase_8k_perf_native_bin_executable_status")).to_equal("hardlink")
expect(_value_of(eight_k, "gui_showcase_8k_perf_reason")).to_equal("missing-8k-native-artifacts:alias_src=pass;native_bin=hardlink;native_bin_executable=hardlink;native_bin_format=pass;native_build_log=pass")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md](doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
