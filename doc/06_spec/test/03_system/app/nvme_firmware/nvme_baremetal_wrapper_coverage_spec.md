# nvme_baremetal_wrapper_coverage_spec

Source: `test/03_system/app/nvme_firmware/nvme_baremetal_wrapper_coverage_spec.spl`

## Purpose

This scenario checks the NVMe baremetal wrapper coverage audit. It does not
claim real RV32 or RV64 boot evidence. It proves the wrapper-evidence surface:
RV32 and RV64 have fail-closed fake-QEMU wrapper self-tests wired into their
SSpecs.

## Scenarios

### reports RV32 and RV64 wrapper coverage in default mode

1. Run `sh scripts/check/check-nvme-baremetal-wrapper-coverage.shs`.
2. Expect exit code `0`.
3. Expect `nvme_baremetal_wrapper_rv32_self_test=pass`.
4. Expect `nvme_baremetal_wrapper_rv32_spec_status=pass`.
5. Expect `nvme_baremetal_wrapper_coverage_status=pass`.
6. Expect `nvme_baremetal_wrapper_coverage_blockers=none`.
7. Expect `nvme_baremetal_wrapper_rv64_self_test=pass`.
8. Expect `nvme_baremetal_wrapper_rv64_spec_status=pass`.
9. Expect `STATUS: PASS nvme-baremetal-wrapper-coverage status=pass blockers=none`.

### passes strict mode when RV32 and RV64 wrapper coverage exists

1. Run `sh scripts/check/check-nvme-baremetal-wrapper-coverage.shs --strict`.
2. Expect exit code `0`.
3. Expect `nvme_baremetal_wrapper_coverage_status=pass`.
4. Expect `nvme_baremetal_wrapper_coverage_blockers=none`.
5. Expect `STATUS: PASS nvme-baremetal-wrapper-coverage status=pass blockers=none`.

### self-tests fake wrapper coverage failure modes

1. Run `sh scripts/check/check-nvme-baremetal-wrapper-coverage.shs --self-test`.
2. Expect exit code `0`.
3. Expect `STATUS: PASS nvme-baremetal-wrapper-coverage self-test`.

## Executable Snippet

```simple
val (out, err, code) = _run("sh scripts/check/check-nvme-baremetal-wrapper-coverage.shs")
expect(code).to_equal(0)
expect(out).to_contain("nvme_baremetal_wrapper_rv32_self_test=pass")
expect(out).to_contain("nvme_baremetal_wrapper_rv64_self_test=pass")
expect(out).to_contain("nvme_baremetal_wrapper_coverage_blockers=none")

val (strict_out, strict_err, strict_code) = _run("sh scripts/check/check-nvme-baremetal-wrapper-coverage.shs --strict")
expect(strict_code).to_equal(0)
expect(strict_out).to_contain("STATUS: PASS nvme-baremetal-wrapper-coverage status=pass blockers=none")

val (self_out, self_err, self_code) = _run("sh scripts/check/check-nvme-baremetal-wrapper-coverage.shs --self-test")
expect(self_code).to_equal(0)
expect(self_out).to_contain("STATUS: PASS nvme-baremetal-wrapper-coverage self-test")
```
