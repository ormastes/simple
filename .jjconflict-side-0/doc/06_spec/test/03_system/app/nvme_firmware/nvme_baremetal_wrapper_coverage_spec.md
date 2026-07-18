# nvme_baremetal_wrapper_coverage_spec

> NVMe baremetal wrapper coverage audit.

<!-- sdn-diagram:id=nvme_baremetal_wrapper_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvme_baremetal_wrapper_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvme_baremetal_wrapper_coverage_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvme_baremetal_wrapper_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# nvme_baremetal_wrapper_coverage_spec

NVMe baremetal wrapper coverage audit.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/nvme_firmware/nvme_baremetal_wrapper_coverage_spec.spl` |
| Updated | 2026-07-07 |
| Generator | `simple spipe-docgen` (Simple) |

NVMe baremetal wrapper coverage audit.

The audit is not real boot evidence. It proves the wrapper-evidence surface:
RV32 and RV64 have fail-closed fake-QEMU self-tests wired into their SSpecs.

## Scenarios

### NVMe baremetal wrapper coverage audit

#### reports RV32 and RV64 wrapper coverage in default mode

- Run the default NVMe baremetal wrapper coverage audit
   - Expected: code equals `0`
- The audit proves RV32 wrapper self-test coverage
- The audit proves RV64 wrapper self-test coverage
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the default NVMe baremetal wrapper coverage audit")
val (out, err, code) = _run("sh scripts/check/check-nvme-baremetal-wrapper-coverage.shs")
expect(code).to_equal(0)

step("The audit proves RV32 wrapper self-test coverage")
expect(out).to_contain("nvme_baremetal_wrapper_rv32_self_test=pass")
expect(out).to_contain("nvme_baremetal_wrapper_rv32_spec_status=pass")

step("The audit proves RV64 wrapper self-test coverage")
expect(out).to_contain("nvme_baremetal_wrapper_coverage_status=pass")
expect(out).to_contain("nvme_baremetal_wrapper_coverage_blockers=none")
expect(out).to_contain("nvme_baremetal_wrapper_rv64_self_test=pass")
expect(out).to_contain("nvme_baremetal_wrapper_rv64_spec_status=pass")
expect(out).to_contain("STATUS: PASS nvme-baremetal-wrapper-coverage status=pass blockers=none")
_expect_no_fail_marker(out, "default wrapper coverage audit")
```

</details>

#### passes strict mode when RV32 and RV64 wrapper coverage exists

- Run strict mode after both wrappers have fail-closed self-test coverage
   - Expected: code equals `0`
- Strict mode reports a complete wrapper coverage pass
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run strict mode after both wrappers have fail-closed self-test coverage")
val (out, err, code) = _run("sh scripts/check/check-nvme-baremetal-wrapper-coverage.shs --strict")
expect(code).to_equal(0)

step("Strict mode reports a complete wrapper coverage pass")
expect(out).to_contain("nvme_baremetal_wrapper_coverage_status=pass")
expect(out).to_contain("nvme_baremetal_wrapper_coverage_blockers=none")
expect(out).to_contain("STATUS: PASS nvme-baremetal-wrapper-coverage status=pass blockers=none")
_expect_no_fail_marker(out, "strict wrapper coverage audit")
```

</details>

#### self-tests fake wrapper coverage failure modes

- Run the wrapper coverage fake-fixture self-test
   - Expected: code equals `0`
- The self-test proves fake missing RV64 and RV32 coverage fail closed
-  expect no fail marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the wrapper coverage fake-fixture self-test")
val (out, err, code) = _run("sh scripts/check/check-nvme-baremetal-wrapper-coverage.shs --self-test")
expect(code).to_equal(0)

step("The self-test proves fake missing RV64 and RV32 coverage fail closed")
expect(out).to_contain("STATUS: PASS nvme-baremetal-wrapper-coverage self-test")
_expect_no_fail_marker(out, "wrapper coverage self-test")
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
