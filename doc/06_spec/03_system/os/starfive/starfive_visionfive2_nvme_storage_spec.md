# StarFive VisionFive 2 NVMe storage safety

Source: `test/03_system/os/starfive/starfive_visionfive2_nvme_storage_spec.spl`

The operator first runs `scripts/check/check-starfive-nvme-storage.shs --contract`
and `--self-test`. These modes inspect code and policy only; they do not access
the board or storage media.

`--identify-live` sends only `nvme identify` over the resolved Tigard UART. It
requires a fresh machine-readable controller/namespace identity, binds it to the
admitted RAM-boot image, and writes an atomic read-only receipt. UART absence or
silence is BLOCKED, never PASS. PCI vendor/device/class/BAR discovery alone is
not an identity receipt.

`--provision-live` is a different authority boundary. It requires the immutable
identity receipt, re-identifies the same namespace, verifies the image and exact
SHA-256 confirmation, then requires the explicit provisioning phrase. Success
requires GPT/FAT32 creation, controller flushes, unmount/remount hash readback,
and a fresh command-correlated public-VFS `ls /nvme` containing `proof.txt`.
A contract PASS never means a device was identified or written.

Expected safe checks:

```sh
scripts/check/check-starfive-nvme-storage.shs --contract
scripts/check/check-starfive-nvme-storage.shs --self-test
scripts/check/check-starfive-nvme-storage.shs --identify-live
scripts/check/check-starfive-nvme-storage.shs --provision-live
```
