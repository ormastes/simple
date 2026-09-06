# nvme_rv64_baremetal_boot_spec

Source: `test/03_system/app/nvme_firmware/nvme_rv64_baremetal_boot_spec.spl`

## Purpose

This scenario checks RV64 NVMe baremetal wrapper evidence. It does not claim a
real RV64 QEMU firmware boot. It proves the wrapper self-test rejects missing
PASS markers and serial `FAIL` markers before the wrapper can count as coverage.

## Scenario

### runs the rv64 boot wrapper fail-closed self-test

1. Run `sh examples/09_embedded/simpleos_nvme_fw/fw_rv64/boot.shs --self-test`.
2. Expect exit code `0`.
3. Expect `STATUS: PASS nvme-rv64-boot self-test`.

## Executable Snippet

```simple
val (out, err, code) = _run("sh examples/09_embedded/simpleos_nvme_fw/fw_rv64/boot.shs --self-test")
expect(code).to_equal(0)
expect(out).to_contain("STATUS: PASS nvme-rv64-boot self-test")
```
