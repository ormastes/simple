# LLM Caret Installed Claude CLI Compatibility

> Checks the currently installed Claude CLI’s offline command contract and
> records drift provenance without sending a prompt or inheriting provider
> credentials.

| Tests | Active | Skipped | Pending |
|-------|-------:|--------:|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application / CLI |
| Status | Active; fails closed when Claude is not installed |
| Requirement support | REQ-LLM-CARET-CLI-HARDEN-006 |
| Plan | `doc/03_plan/sys_test/llm_caret_cli_tui_hardening.md` |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli_spec.spl` |
| Updated | 2026-07-24 |
| Generator | Manual synchronization; installed probe execution is a separate gate |

## Scope

The checker resolves the installed `claude` command and its canonical target,
then records its version and SHA-256 without accepting either value as a pinned
release requirement. Every child gets a fresh `HOME`, `CLAUDE_CONFIG_DIR`, and
working directory under a per-invocation temporary root outside the repository.
The child starts through `env -i` with only HOME/config, a command-search path,
fixed locale/TERM, and nonessential-traffic disablement, so host provider
credentials and repository-parent settings are not inherited.

The executable cases use only `--version`, `--help`, missing `-p` input, and
the removed `--max-tokens` option. There is no successful prompt-bearing case,
session resume, authentication, inherited provider credential, or accepted
provider response.
This is supplemental environmental compatibility evidence; direct
production-declaration scenarios remain the authoritative requirement proof.

**Artifacts:**
`build/test-artifacts/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli/`

## Scenarios

### REQ-LLM-CARET-CLI-HARDEN-006: installed Claude CLI contract

#### should resolve the installed executable and recorded provenance

- Load the accepted Claude feature map.
- Invoke the installed Claude CLI with no prompt or provider credentials.
- Check the structured CLI response.
  - Expected: executable path, canonical target, SHA-256, and raw artifacts are
    present.
  - Expected: missing or non-executable Claude fails closed.

<details>
<summary>Executable SSpec</summary>

```simple
step("Load the accepted Claude feature map")
check_feature_map()

step("Invoke the installed Claude CLI with no prompt or provider credentials")
val result = probe_current_claude_cli("prerequisites")

step("Check the structured CLI response")
expect(result.stdout).to_contain(
    "case=prerequisites status=PASS"
)
expect(result.stdout).to_contain("claude_path=")
expect(result.stdout).to_contain("claude_canonical_target=")
expect(result.stdout).to_contain("claude_sha256=")
expect(result.stdout).to_contain("prompt_submitted=false")
expect(result.stdout).to_contain(
    "provider_credentials_inherited=false"
)
expect(result.stdout).to_contain("evidence_status=PASS")
expect(result.stdout).to_contain(ARTIFACT_ROOT)
expect(result.exit_code).to_equal(0)
check_probe_artifacts("prerequisites")
```

</details>

#### should record the current version without pinning release drift

- Load the accepted Claude feature map.
- Invoke the installed Claude CLI with no prompt or provider credentials.
- Check the structured CLI response.
  - Expected: a nonempty version and zero raw exit are recorded.
  - Expected: the scenario does not hardcode an exact version or hash.

<details>
<summary>Executable SSpec</summary>

```simple
step("Load the accepted Claude feature map")
check_feature_map()

step("Invoke the installed Claude CLI with no prompt or provider credentials")
val result = probe_current_claude_cli("version")

step("Check the structured CLI response")
expect(result.stdout).to_contain("case=version status=PASS")
expect(result.stdout).to_contain("claude_version=")
expect(result.stdout).to_contain("version_recorded=true")
expect(result.stdout).to_contain("raw_exit=0")
expect(result.stdout).to_contain("prompt_submitted=false")
expect(result.exit_code).to_equal(0)
check_probe_artifacts("version")
```

</details>

#### should advertise every required current flag and variadic allowed tools

- Load the accepted Claude feature map.
- Invoke the installed Claude CLI with no prompt or provider credentials.
- Check the structured CLI response.
  - Expected: Caret’s current Claude arguments are advertised.
  - Expected: `--allowedTools` is variadic and `--max-tokens` is absent.

<details>
<summary>Executable SSpec</summary>

```simple
step("Load the accepted Claude feature map")
check_feature_map()

step("Invoke the installed Claude CLI with no prompt or provider credentials")
val result = probe_current_claude_cli("help")

step("Check the structured CLI response")
expect(result.stdout).to_contain("case=help status=PASS")
expect(result.stdout).to_contain("required_flags=present")
expect(result.stdout).to_contain("allowed_tools_variadic=true")
expect(result.stdout).to_contain(
    "removed_max_tokens_absent=true"
)
expect(result.stdout).to_contain("prompt_submitted=false")
expect(result.exit_code).to_equal(0)
check_probe_artifacts("help")
```

</details>

#### should reject missing print input without a prompt-bearing provider path

- Load the accepted Claude feature map.
- Invoke the installed Claude CLI with no prompt or provider credentials.
- Check the structured CLI response.
  - Expected: closed stdin with `-p` exits nonzero and names missing input,
    prompt, or stdin.
  - Expected: the result claims only input rejection, not unrelated verbose
    validation.

<details>
<summary>Executable SSpec</summary>

```simple
step("Load the accepted Claude feature map")
check_feature_map()

step("Invoke the installed Claude CLI with no prompt or provider credentials")
val result = probe_current_claude_cli("missing-input")

step("Check the structured CLI response")
expect(result.stdout).to_contain(
    "case=missing-input status=PASS"
)
expect(result.stdout).to_contain("input_rejected=true")
expect(result.stdout).to_contain("prompt_submitted=false")
expect(result.exit_code).to_equal(0)
check_probe_artifacts("missing-input")
```

</details>

#### should safely reject the removed maximum-token option

- Load the accepted Claude feature map.
- Invoke the installed Claude CLI with no prompt or provider credentials.
- Check the structured CLI response.
  - Expected: `--max-tokens` exits nonzero and is named in raw diagnostics.
  - Expected: no prompt-bearing success is possible.

<details>
<summary>Executable SSpec</summary>

```simple
step("Load the accepted Claude feature map")
check_feature_map()

step("Invoke the installed Claude CLI with no prompt or provider credentials")
val result = probe_current_claude_cli("removed-option")

step("Check the structured CLI response")
expect(result.stdout).to_contain(
    "case=removed-option status=PASS"
)
expect(result.stdout).to_contain(
    "removed_option_rejected=true"
)
expect(result.stdout).to_contain("prompt_submitted=false")
expect(result.exit_code).to_equal(0)
check_probe_artifacts("removed-option")
```

</details>

</details>

<details>
<summary>Executable helper source</summary>

```simple
use app.io.mod.{file_exists, file_read, process_run_bounded}

val FEATURE_MAP = "doc/03_plan/trace/llm_caret_claude_cli_full_parity_feature_matrix.tsv"
val CHECKER = "scripts/check/check-llm-caret-installed-claude-cli.shs"
val ARTIFACT_ROOT = "build/test-artifacts/03_system/app/llm_caret/feature/llm_caret_installed_claude_cli"

struct ClaudeCliProbeResult:
    stdout: text
    stderr: text
    exit_code: i64

fn probe_current_claude_cli(case_name: text) -> ClaudeCliProbeResult:
    val (stdout, stderr, exit_code) = process_run_bounded(
        "sh",
        [CHECKER, "--case", case_name],
        20000,
        32768
    )
    ClaudeCliProbeResult(
        stdout: stdout,
        stderr: stderr,
        exit_code: exit_code
    )

fn check_feature_map():
    expect(file_exists(FEATURE_MAP)).to_be(true)
    expect(file_read(FEATURE_MAP)).to_contain("\tcli\t")

fn check_probe_artifacts(case_name: text):
    val case_root = ARTIFACT_ROOT + "/" + case_name
    expect(file_exists(case_root + "/stdout.txt")).to_be(true)
    expect(file_exists(case_root + "/stderr.txt")).to_be(true)
    expect(file_exists(case_root + "/exit.txt")).to_be(true)
    expect(file_exists(case_root + "/claude-path.txt")).to_be(true)
    expect(file_exists(case_root + "/claude-canonical-target.txt")).to_be(true)
    expect(file_exists(case_root + "/claude-version.txt")).to_be(true)
    expect(file_exists(case_root + "/claude-sha256.txt")).to_be(true)
    expect(file_read(case_root + "/claude-sha256.txt").len()).to_be_greater_than(63)
```

The helper invokes only the repository checker. Each checker child is bounded
to five seconds and each raw stdout/stderr file to a conservative 64 KiB; the
outer SSpec allows 20 seconds for discovery plus the metadata and selected-case
children while bounding its own returned output to 32 KiB. Neither layer
declares a leaf runtime extern.

</details>

## Evidence Boundary

Passing evidence proves the installed executable’s current offline CLI surface
matches the Caret wrapper’s bounded argument assumptions. It does not prove
authentication, provider availability, model quality, billing, network
behavior, or an exact pinned Claude release.
