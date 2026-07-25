# test_daemon_execution_session_spec

> Test Daemon Execution Session Specification

<!-- sdn-diagram:id=test_daemon_execution_session_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_daemon_execution_session_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_daemon_execution_session_spec -> std
test_daemon_execution_session_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_daemon_execution_session_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_daemon_execution_session_spec

Test Daemon Execution Session Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TDMN-071 to #TDMN-090 |
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/app/test_daemon/test_daemon_execution_session_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Test Daemon Execution Session Specification

Tests execution session management using the actual session_types and
session_broker implementations: TestSessionMeta, SessionKey, SessionDescriptor
construction from metadata, name converters, and categorization helpers.

## Scenarios

### Execution Sessions

### TestSessionMeta defaults

#### creates default meta with LOCAL kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val meta = test_session_meta_default("test/unit/foo_spec.spl")
expect(meta_needs_session(meta)).to_equal(false)
```

</details>

#### QEMU meta needs a session

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val meta = test_session_meta_default("test/unit/foo_spec.spl")
val key = meta_to_session_key(meta)
expect(key.kind).to_equal(SESSION_KIND_LOCAL)
expect(key.artifact_hash).to_equal("")
```

</details>

#### session_key_matches compares correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = SessionKey(
    kind: SESSION_KIND_CONTAINER,
    target: "docker",
    artifact_hash: "",
    env_profile: "",
    reuse_mode: REUSE_EXCLUSIVE_REUSED,
    reset_policy: RESET_SOFT
)
val desc = session_descriptor_new(key)
expect(desc.timeout_ms).to_equal(60000)
expect(desc.max_concurrent).to_equal(1)
expect(desc.key.kind).to_equal(SESSION_KIND_CONTAINER)
```

</details>

### SessionLease creation

#### creates lease in IDLE state

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
expect(lease.pid).to_equal(0)
expect(lease.test_count).to_equal(0)
expect(lease.key.kind).to_equal(SESSION_KIND_SERVICE)
```

</details>

#### lease session_id matches key_to_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val meta = parse_session_meta("test/unit/foo_spec.spl", [])
expect(meta.session_kind).to_equal(SESSION_KIND_LOCAL)
expect(meta.reuse_mode).to_equal(REUSE_FRESH_PER_TEST)
```

</details>

### name converters

#### converts session kind to name and back

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(reuse_mode_name(REUSE_SHARED_READ_ONLY)).to_equal("shared_read_only")
expect(reuse_mode_name(REUSE_FRESH_PER_TEST)).to_equal("fresh_per_test")
expect(reuse_mode_from_name("shared_with_reset")).to_equal(REUSE_SHARED_WITH_RESET)
expect(reuse_mode_from_name("bogus")).to_equal(-1)
```

</details>

#### converts reset policy to name and back

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(reset_policy_name(RESET_NONE)).to_equal("none")
expect(reset_policy_name(RESET_RECREATE)).to_equal("recreate")
expect(reset_policy_from_name("hard_reset")).to_equal(RESET_HARD)
expect(reset_policy_from_name("reload_binary")).to_equal(RESET_RELOAD_BINARY)
expect(reset_policy_from_name("nope")).to_equal(-1)
```

</details>

### execution strategy

#### categorizes QEMU test files

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(categorize_test_file("test/unit/lib/qemu/boot_spec.spl")).to_equal("qemu")
expect(categorize_test_file("test/emulator/arm64_spec.spl")).to_equal("qemu")
```

</details>

#### categorizes baremetal test files

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(categorize_test_file("test/baremetal/kernel_init_spec.spl")).to_equal("baremetal")
expect(categorize_test_file("test/kernel/boot_spec.spl")).to_equal("baremetal")
```

</details>

#### categorizes standard test files

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(categorize_test_file("test/unit/parser/lexer_spec.spl")).to_equal("unit")
expect(categorize_test_file("test/integration/api_spec.spl")).to_equal("integration")
expect(categorize_test_file("test/system/daemon_spec.spl")).to_equal("system")
```

</details>

#### assigns correct timeouts per category

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(strategy_timeout_for_category("qemu")).to_equal(1800)
expect(strategy_timeout_for_category("baremetal")).to_equal(1800)
expect(strategy_timeout_for_category("unit")).to_equal(60)
expect(strategy_timeout_for_category("system")).to_equal(600)
```

</details>

#### assigns correct memory per category

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
