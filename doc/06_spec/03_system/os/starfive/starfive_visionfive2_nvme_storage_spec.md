# StarFive VisionFive 2 NVMe storage safety

Source: `test/03_system/os/starfive/starfive_visionfive2_nvme_storage_spec.spl`

The operator first runs `scripts/check/check-starfive-nvme-storage.shs --contract`
and `--self-test`. These modes inspect code and policy only; they do not access
the board or storage media.

`--identify-live` is read-only only. NVMe `nvme identify` command plumbing now
exists in board firmware, so this mode no longer blocks on “command not
implemented.” It still exits 2 (`starfive_nvme_status=blocked`) until physical
UART evidence is collected from a live StarFive session. PCI vendor/device/class/
BAR discovery is not itself an identity receipt.

`--provision-live` is a different authority boundary. It requires the exact
environment authorization phrase and an immutable identity receipt path, then
still exits BLOCKED until identity revalidation, mounted/in-use/boot-source
exclusion, GPT, FAT32, flush/remount verification, and public-VFS `ls /nvme`
are implemented. A contract PASS never means a device was identified or written.

Expected safe checks:

```sh
scripts/check/check-starfive-nvme-storage.shs --contract
scripts/check/check-starfive-nvme-storage.shs --self-test
scripts/check/check-starfive-nvme-storage.shs --identify-live
scripts/check/check-starfive-nvme-storage.shs --provision-live
```
