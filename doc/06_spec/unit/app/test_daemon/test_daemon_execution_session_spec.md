# test_daemon_execution_session_spec

> Purpose: Prove that Execution Sessions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_daemon_execution_session_spec

Purpose: Prove that Execution Sessions.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/test_daemon/test_daemon_execution_session_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Execution Sessions.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### Execution Sessions

### TestSessionMeta defaults

#### creates default meta with LOCAL kind

- creates default meta with LOCAL kind
- Verify: creates default meta with LOCAL kind
   - Expected: meta.file_path equals `test/unit/parser_spec.spl`
   - Expected: meta.session_kind equals `SESSION_KIND_LOCAL`
   - Expected: meta.reuse_mode equals `REUSE_FRESH_PER_TEST`
   - Expected: meta.reset_policy equals `RESET_NONE`
   - Expected: meta.target equals ``
   - Expected: meta.artifact equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates default meta with LOCAL kind")
step("Verify: creates default meta with LOCAL kind")
# @req: REQ-APP-TEST-DAEMON-001
val meta = test_session_meta_default("test/unit/parser_spec.spl")
expect(meta.file_path).to_equal("test/unit/parser_spec.spl")
expect(meta.session_kind).to_equal(SESSION_KIND_LOCAL)
expect(meta.reuse_mode).to_equal(REUSE_FRESH_PER_TEST)
expect(meta.reset_policy).to_equal(RESET_NONE)
expect(meta.target).to_equal("")
expect(meta.artifact).to_equal("")
```

</details>

#### default meta does not need a session

- default meta does not need a session
- Verify: default meta does not need a session
   - Expected: meta_needs_session(meta) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default meta does not need a session")
step("Verify: default meta does not need a session")
val meta = test_session_meta_default("test/unit/foo_spec.spl")
expect(meta_needs_session(meta)).to_equal(false)
```

</details>

#### QEMU meta needs a session

- QEMU meta needs a session
- Verify: QEMU meta needs a session
   - Expected: meta_needs_session(meta) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("QEMU meta needs a session")
step("Verify: QEMU meta needs a session")
val meta = TestSessionMeta(
    file_path: "test/baremetal/boot_spec.spl",
    session_kind: SESSION_KIND_QEMU_VM,
    target: "riscv64",
    reuse_mode: REUSE_SHARED_WITH_RESET,
    reset_policy: RESET_RELOAD_BINARY,
    artifact: "/tmp/boot.elf",
    startup_cmd: "",
    healthcheck: ""
)
expect(meta_needs_session(meta)).to_equal(true)
```

</details>

### SessionKey construction

#### builds key from QEMU meta

- builds key from QEMU meta
- Verify: builds key from QEMU meta
   - Expected: key.kind equals `SESSION_KIND_QEMU_VM`
   - Expected: key.target equals `arm64`
   - Expected: key.reuse_mode equals `REUSE_SHARED_WITH_RESET`
   - Expected: key.reset_policy equals `RESET_RELOAD_BINARY`
   - Expected: key.artifact_hash != "" is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds key from QEMU meta")
step("Verify: builds key from QEMU meta")
val meta = TestSessionMeta(
    file_path: "test/baremetal/arm64_boot_spec.spl",
    session_kind: SESSION_KIND_QEMU_VM,
    target: "arm64",
    reuse_mode: REUSE_SHARED_WITH_RESET,
    reset_policy: RESET_RELOAD_BINARY,
    artifact: "/tmp/boot.elf",
    startup_cmd: "",
    healthcheck: ""
)
val key = meta_to_session_key(meta)
expect(key.kind).to_equal(SESSION_KIND_QEMU_VM)
expect(key.target).to_equal("arm64")
expect(key.reuse_mode).to_equal(REUSE_SHARED_WITH_RESET)
expect(key.reset_policy).to_equal(RESET_RELOAD_BINARY)
# artifact_hash should be non-empty because artifact is set
expect(key.artifact_hash != "").to_equal(true)
```

</details>

#### builds key with empty artifact hash for local

- builds key with empty artifact hash for local
- Verify: builds key with empty artifact hash for local
   - Expected: key.kind equals `SESSION_KIND_LOCAL`
   - Expected: key.artifact_hash equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds key with empty artifact hash for local")
step("Verify: builds key with empty artifact hash for local")
val meta = test_session_meta_default("test/unit/foo_spec.spl")
val key = meta_to_session_key(meta)
expect(key.kind).to_equal(SESSION_KIND_LOCAL)
expect(key.artifact_hash).to_equal("")
```

</details>

#### session_key_matches compares correctly

- session_key_matches compares correctly
- Verify: session_key_matches compares correctly
   - Expected: session_key_matches(key_a, key_b) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("session_key_matches compares correctly")
step("Verify: session_key_matches compares correctly")
val key_a = SessionKey(
    kind: SESSION_KIND_QEMU_VM,
    target: "riscv64",
    artifact_hash: "abc123",
    env_profile: "",
    reuse_mode: REUSE_SHARED_WITH_RESET,
    reset_policy: RESET_RELOAD_BINARY
)
val key_b = SessionKey(
    kind: SESSION_KIND_QEMU_VM,
    target: "riscv64",
    artifact_hash: "abc123",
    env_profile: "",
    reuse_mode: REUSE_SHARED_WITH_RESET,
    reset_policy: RESET_HARD
)
# Matches ignores reset_policy — only checks kind/target/hash/profile/reuse
expect(session_key_matches(key_a, key_b)).to_equal(true)
```

</details>

#### session_key_matches rejects different targets

- session_key_matches rejects different targets
- Verify: session_key_matches rejects different targets
   - Expected: session_key_matches(key_a, key_b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("session_key_matches rejects different targets")
step("Verify: session_key_matches rejects different targets")
val key_a = SessionKey(
    kind: SESSION_KIND_QEMU_VM,
    target: "riscv64",
    artifact_hash: "",
    env_profile: "",
    reuse_mode: REUSE_SHARED_WITH_RESET,
    reset_policy: RESET_NONE
)
val key_b = SessionKey(
    kind: SESSION_KIND_QEMU_VM,
    target: "arm64",
    artifact_hash: "",
    env_profile: "",
    reuse_mode: REUSE_SHARED_WITH_RESET,
    reset_policy: RESET_NONE
)
expect(session_key_matches(key_a, key_b)).to_equal(false)
```

</details>

### SessionDescriptor creation

#### creates descriptor with default timeout

- creates descriptor with default timeout
- Verify: creates descriptor with default timeout
   - Expected: desc.timeout_ms equals `60000`
   - Expected: desc.max_concurrent equals `1`
   - Expected: desc.key.kind equals `SESSION_KIND_CONTAINER`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates descriptor with default timeout")
step("Verify: creates descriptor with default timeout")
val key = SessionKey(
    kind: SESSION_KIND_CONTAINER,
    target: "docker",
    artifact_hash: "",
    env_profile: "",
    reuse_mode: REUSE_EXCLUSIVE_REUSED,
    reset_policy: RESET_SOFT
)
val desc = session_descriptor_new(key)
expect(desc.timeout_ms).to_equal(60000)  # oracle: 60000 — named expected value from the requirement
expect(desc.max_concurrent).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(desc.key.kind).to_equal(SESSION_KIND_CONTAINER)
```

</details>

### SessionLease creation

#### creates lease in IDLE state

- creates lease in IDLE state
- Verify: creates lease in IDLE state
   - Expected: lease.status equals `LEASE_IDLE`
   - Expected: lease.pid equals `0`
   - Expected: lease.test_count equals `0`
   - Expected: lease.key.kind equals `SESSION_KIND_SERVICE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates lease in IDLE state")
step("Verify: creates lease in IDLE state")
val key = SessionKey(
    kind: SESSION_KIND_SERVICE,
    target: "http_server",
    artifact_hash: "",
    env_profile: "",
    reuse_mode: REUSE_SHARED_READ_ONLY,
    reset_policy: RESET_NONE
)
val lease = session_lease_new(key)
expect(lease.status).to_equal(LEASE_IDLE)
expect(lease.pid).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(lease.test_count).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(lease.key.kind).to_equal(SESSION_KIND_SERVICE)
```

</details>

#### lease session_id matches key_to_id

- lease session_id matches key_to_id
- Verify: lease session_id matches key_to_id
   - Expected: lease.session_id equals `expected_id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lease session_id matches key_to_id")
step("Verify: lease session_id matches key_to_id")
val key = SessionKey(
    kind: SESSION_KIND_QEMU_VM,
    target: "riscv64",
    artifact_hash: "h123",
    env_profile: "",
    reuse_mode: REUSE_SHARED_WITH_RESET,
    reset_policy: RESET_RELOAD_BINARY
)
val lease = session_lease_new(key)
val expected_id = session_key_to_id(key)
expect(lease.session_id).to_equal(expected_id)
```

</details>

### session_key_to_id

#### generates readable ID from key

- generates readable ID from key
- Verify: generates readable ID from key


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates readable ID from key")
step("Verify: generates readable ID from key")
val key = SessionKey(
    kind: SESSION_KIND_QEMU_VM,
    target: "arm64",
    artifact_hash: "deadbeef",
    env_profile: "",
    reuse_mode: REUSE_SHARED_WITH_RESET,
    reset_policy: RESET_NONE
)
val id = session_key_to_id(key)
expect(id).to_contain("qemu_vm")
expect(id).to_contain("arm64")
expect(id).to_contain("deadbeef")
```

</details>

### parse_session_meta

#### parses session-kind marker

- parses session-kind marker
- Verify: parses session-kind marker
   - Expected: meta.session_kind equals `SESSION_KIND_QEMU_VM`
   - Expected: meta.target equals `riscv64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses session-kind marker")
step("Verify: parses session-kind marker")
val lines = [
    "# @session-kind: qemu_vm",
    "# @target: riscv64"
]
val meta = parse_session_meta("test/boot_spec.spl", lines)
expect(meta.session_kind).to_equal(SESSION_KIND_QEMU_VM)
expect(meta.target).to_equal("riscv64")
```

</details>

#### parses reuse and reset markers

- parses reuse and reset markers
- Verify: parses reuse and reset markers
   - Expected: meta.session_kind equals `SESSION_KIND_CONTAINER`
   - Expected: meta.reuse_mode equals `REUSE_SHARED_WITH_RESET`
   - Expected: meta.reset_policy equals `RESET_SOFT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses reuse and reset markers")
step("Verify: parses reuse and reset markers")
val lines = [
    "# @session-kind: container_instance",
    "# @reuse: shared_with_reset",
    "# @reset: soft_reset"
]
val meta = parse_session_meta("test/db_spec.spl", lines)
expect(meta.session_kind).to_equal(SESSION_KIND_CONTAINER)
expect(meta.reuse_mode).to_equal(REUSE_SHARED_WITH_RESET)
expect(meta.reset_policy).to_equal(RESET_SOFT)
```

</details>

#### parses artifact and startup markers

- parses artifact and startup markers
- Verify: parses artifact and startup markers
   - Expected: meta.artifact equals `/tmp/test.elf`
   - Expected: meta.startup_cmd equals `qemu-system-riscv64 -kernel /tmp/test.elf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses artifact and startup markers")
step("Verify: parses artifact and startup markers")
val lines = [
    "# @session-kind: qemu_vm",
    "# @artifact: /tmp/test.elf",
    "# @startup: qemu-system-riscv64 -kernel /tmp/test.elf"
]
val meta = parse_session_meta("test/boot_spec.spl", lines)
expect(meta.artifact).to_equal("/tmp/test.elf")
expect(meta.startup_cmd).to_equal("qemu-system-riscv64 -kernel /tmp/test.elf")
```

</details>

#### returns defaults for empty header

- returns defaults for empty header
- Verify: returns defaults for empty header
   - Expected: meta.session_kind equals `SESSION_KIND_LOCAL`
   - Expected: meta.reuse_mode equals `REUSE_FRESH_PER_TEST`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns defaults for empty header")
step("Verify: returns defaults for empty header")
val meta = parse_session_meta("test/unit/foo_spec.spl", [])
expect(meta.session_kind).to_equal(SESSION_KIND_LOCAL)
expect(meta.reuse_mode).to_equal(REUSE_FRESH_PER_TEST)
```

</details>

### name converters

#### converts session kind to name and back

- converts session kind to name and back
- Verify: converts session kind to name and back
   - Expected: session_kind_name(SESSION_KIND_QEMU_VM) equals `qemu_vm`
   - Expected: session_kind_name(SESSION_KIND_CONTAINER) equals `container_instance`
   - Expected: session_kind_name(SESSION_KIND_GUI) equals `gui_session`
   - Expected: session_kind_name(SESSION_KIND_LOCAL) equals `local`
   - Expected: session_kind_from_name("qemu_vm") equals `SESSION_KIND_QEMU_VM`
   - Expected: session_kind_from_name("local") equals `SESSION_KIND_LOCAL`
   - Expected: session_kind_from_name("unknown_thing") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts session kind to name and back")
step("Verify: converts session kind to name and back")
expect(session_kind_name(SESSION_KIND_QEMU_VM)).to_equal("qemu_vm")
expect(session_kind_name(SESSION_KIND_CONTAINER)).to_equal("container_instance")
expect(session_kind_name(SESSION_KIND_GUI)).to_equal("gui_session")
expect(session_kind_name(SESSION_KIND_LOCAL)).to_equal("local")
expect(session_kind_from_name("qemu_vm")).to_equal(SESSION_KIND_QEMU_VM)
expect(session_kind_from_name("local")).to_equal(SESSION_KIND_LOCAL)
expect(session_kind_from_name("unknown_thing")).to_equal(-1)
```

</details>

#### converts reuse mode to name and back

- converts reuse mode to name and back
- Verify: converts reuse mode to name and back
   - Expected: reuse_mode_name(REUSE_SHARED_READ_ONLY) equals `shared_read_only`
   - Expected: reuse_mode_name(REUSE_FRESH_PER_TEST) equals `fresh_per_test`
   - Expected: reuse_mode_from_name("shared_with_reset") equals `REUSE_SHARED_WITH_RESET`
   - Expected: reuse_mode_from_name("bogus") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts reuse mode to name and back")
step("Verify: converts reuse mode to name and back")
expect(reuse_mode_name(REUSE_SHARED_READ_ONLY)).to_equal("shared_read_only")
expect(reuse_mode_name(REUSE_FRESH_PER_TEST)).to_equal("fresh_per_test")
expect(reuse_mode_from_name("shared_with_reset")).to_equal(REUSE_SHARED_WITH_RESET)
expect(reuse_mode_from_name("bogus")).to_equal(-1)
```

</details>

#### converts reset policy to name and back

- converts reset policy to name and back
- Verify: converts reset policy to name and back
   - Expected: reset_policy_name(RESET_NONE) equals `none`
   - Expected: reset_policy_name(RESET_RECREATE) equals `recreate`
   - Expected: reset_policy_from_name("hard_reset") equals `RESET_HARD`
   - Expected: reset_policy_from_name("reload_binary") equals `RESET_RELOAD_BINARY`
   - Expected: reset_policy_from_name("nope") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts reset policy to name and back")
step("Verify: converts reset policy to name and back")
expect(reset_policy_name(RESET_NONE)).to_equal("none")
expect(reset_policy_name(RESET_RECREATE)).to_equal("recreate")
expect(reset_policy_from_name("hard_reset")).to_equal(RESET_HARD)
expect(reset_policy_from_name("reload_binary")).to_equal(RESET_RELOAD_BINARY)
expect(reset_policy_from_name("nope")).to_equal(-1)
```

</details>

### execution strategy

#### categorizes QEMU test files

- categorizes QEMU test files
- Verify: categorizes QEMU test files
   - Expected: categorize_test_file("test/unit/lib/qemu/boot_spec.spl") equals `qemu`
   - Expected: categorize_test_file("test/emulator/arm64_spec.spl") equals `qemu`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("categorizes QEMU test files")
step("Verify: categorizes QEMU test files")
expect(categorize_test_file("test/unit/lib/qemu/boot_spec.spl")).to_equal("qemu")
expect(categorize_test_file("test/emulator/arm64_spec.spl")).to_equal("qemu")
```

</details>

#### categorizes baremetal test files

- categorizes baremetal test files
- Verify: categorizes baremetal test files
   - Expected: categorize_test_file("test/baremetal/kernel_init_spec.spl") equals `baremetal`
   - Expected: categorize_test_file("test/kernel/boot_spec.spl") equals `baremetal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("categorizes baremetal test files")
step("Verify: categorizes baremetal test files")
expect(categorize_test_file("test/baremetal/kernel_init_spec.spl")).to_equal("baremetal")
expect(categorize_test_file("test/kernel/boot_spec.spl")).to_equal("baremetal")
```

</details>

#### categorizes standard test files

- categorizes standard test files
- Verify: categorizes standard test files
   - Expected: categorize_test_file("test/unit/parser/lexer_spec.spl") equals `unit`
   - Expected: categorize_test_file("test/integration/api_spec.spl") equals `integration`
   - Expected: categorize_test_file("test/system/daemon_spec.spl") equals `system`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("categorizes standard test files")
step("Verify: categorizes standard test files")
expect(categorize_test_file("test/unit/parser/lexer_spec.spl")).to_equal("unit")
expect(categorize_test_file("test/integration/api_spec.spl")).to_equal("integration")
expect(categorize_test_file("test/system/daemon_spec.spl")).to_equal("system")
```

</details>

#### assigns correct timeouts per category

- assigns correct timeouts per category
- Verify: assigns correct timeouts per category
   - Expected: strategy_timeout_for_category("qemu") equals `1800`
   - Expected: strategy_timeout_for_category("baremetal") equals `1800`
   - Expected: strategy_timeout_for_category("unit") equals `60`
   - Expected: strategy_timeout_for_category("system") equals `600`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns correct timeouts per category")
step("Verify: assigns correct timeouts per category")
expect(strategy_timeout_for_category("qemu")).to_equal(1800)
expect(strategy_timeout_for_category("baremetal")).to_equal(1800)
expect(strategy_timeout_for_category("unit")).to_equal(60)
expect(strategy_timeout_for_category("system")).to_equal(600)
```

</details>

#### assigns correct memory per category

- assigns correct memory per category
- Verify: assigns correct memory per category
   - Expected: strategy_memory_mb_for_category("qemu") equals `2048`
   - Expected: strategy_memory_mb_for_category("unit") equals `256`
   - Expected: strategy_memory_mb_for_category("system") equals `1024`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns correct memory per category")
step("Verify: assigns correct memory per category")
expect(strategy_memory_mb_for_category("qemu")).to_equal(2048)
expect(strategy_memory_mb_for_category("unit")).to_equal(256)
expect(strategy_memory_mb_for_category("system")).to_equal(1024)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-APP-TEST-DAEMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a3cdd7eb3a31e4aad1e6d2c2b2f74fa1e7250e97c974f0362c3abd26d1ee4be7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a3cdd7eb3a31e4aad1e6d2c2b2f74fa1e7250e97c974f0362c3abd26d1ee4be7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a3cdd7eb3a31e4aad1e6d2c2b2f74fa1e7250e97c974f0362c3abd26d1ee4be7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/test_daemon/test_daemon_execution_session_spec.spl
mirror: doc/06_spec/unit/app/test_daemon/test_daemon_execution_session_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/test_daemon/test_daemon_execution_session_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/test_daemon/test_daemon_execution_session_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/test_daemon/test_daemon_execution_session_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/test_daemon/test_daemon_execution_session_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates default meta with LOCAL kind' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_daemon/test_daemon_execution_session_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'default meta does not need a session' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_daemon/test_daemon_execution_session_spec.spl:119:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'QEMU meta needs a session' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
