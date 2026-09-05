# Domain research: ARM QEMU and Arduino UNO Q servers

## QEMU ARM virt

Official QEMU documentation identifies `virt` as the generic AArch64 platform.
It supplies PCI/PCIe and 32 virtio-mmio transports but no default storage or
network device; the launcher must add a virtio NIC and backend explicitly.
QEMU's documented AArch64 example uses `virtio-net-pci` plus user networking
and host port forwarding. On an x86_64 host, TCG is correctness emulation; KVM
for AArch64 guests requires an AArch64 host.

Sources:

- https://qemu.readthedocs.io/en/v7.2.19/system/arm/virt.html
- https://qemu.readthedocs.io/en/v8.2.10/system/introduction.html
- https://qemu.readthedocs.io/en/master/system/devices/net.html

## Arduino UNO Q

Arduino's official product documentation describes UNO Q as a dual-processor
board: a Qualcomm QRB2210 Cortex-A53 MPU running Debian Linux and an STM32U585
Cortex-M33 MCU running the Arduino/Zephyr side. It exposes an Adreno GPU, eMMC,
Wi-Fi and the Bridge RPC between MPU and MCU. Debian is therefore the vendor
default, not proof that this repository's SimpleOS port booted.

The physical acceptance row must retain a repository-owned SimpleOS boot or
download path, target transcript, filesystem executable hash and protocol
evidence. Board identity, Vulkan enumeration, or Debian execution alone is only
host readiness.

Sources:

- https://docs.arduino.cc/hardware/uno-q/
- https://docs.arduino.cc/resources/datasheets/ABX00162-datasheet.pdf

## 2026-08-14 signed boot and recovery findings

Arduino documents regular USB mode as VID:PID `2341:0078` and recovery flashing
through Qualcomm Emergency Download Mode as `05c6:9008`. Its supported Linux
image recovery owners are Arduino App Lab and Arduino Flasher CLI; this is
evidence for a recoverable vendor-image path, not permission or documentation
for flashing an arbitrary SimpleOS image. The public material found in this
review does not publish the UNO Q signing keys, authenticated partition
manifest, rollback-index policy, or a supported custom-OS boot slot.

Consequently, the only safe future SimpleOS route is to preserve the vendor
secure boot chain and use an Arduino/Qualcomm-authorized signed payload and
board-specific download manifest. Raw Firehose/EDL tools, guessed partitions,
bootloader unlocks, or overwriting the Debian rootfs are not admissible.

Sources:

- [Arduino UNO Q user manual](https://github.com/arduino/docs-content/blob/main/content/hardware/02.uno/boards/uno-q/tutorials/01.user-manual/content.md)
- [Arduino App Lab documentation](https://docs.arduino.cc/software/app-lab/)
- [Arduino UNO Q datasheet](https://docs.arduino.cc/resources/datasheets/ABX00162-datasheet.pdf)

## 2026-08-14 authoritative trust-root follow-up

<!-- codex-research -->

Official public sources provide a usable **factory recovery transport**, but do
not provide the authority needed to sign or admit a custom SimpleOS boot chain:

- Arduino's UNO Q manual identifies normal USB as `2341:0078`, Qualcomm EDL as
  `05c6:9008`, and names Arduino App Lab / Arduino Flasher CLI as the supported
  Linux-image recovery owners. It does not document custom-OS key enrollment,
  rollback-index allocation, or an owner signing key.
- Arduino's official `arduino-deb-images` recipe pins the UNO Q/Imola rescue
  archive `unoq-bootloader-emmc-linux-251020.zip` by SHA-256
  `c606e95d0107f8c58d0dd9494e00624d1db7c4361cca20513bc78ef02ca28dd1`.
  This authenticates the expected factory input only to the extent the recipe
  itself is trusted; it is not a SimpleOS signature or signing authorization.
- Arduino's GPL-3.0-or-later flasher embeds an EDL Firehose programmer and
  invokes QDL with `rawprogram0.xml` / `patch0.xml`. Its registry obtains
  `info.json` over HTTPS and checks the archive against SHA-256 from that same
  JSON. It exposes no detached manifest signature, pinned manifest key,
  rollback index, or custom payload authorization. It also accepts local
  archives, so a successful flash alone does not prove vendor provenance.
- Qualcomm confirms QRB2210 has secure boot, secure key provisioning, secure
  debug, and TrustZone, but does not publish an UNO Q owner root, signing
  service, fuse policy, rollback contract, or custom-image authorization.

The missing trust root therefore cannot legitimately be reconstructed from the
public repositories. The image-recipe source is BSD-3-Clause and the flasher is
GPL-3.0-or-later, but code licences neither confer signing authority nor state
the redistribution terms of every binary in the separately hosted rescue
archive. This audit did not download or inspect that archive.

Safe next action: ask Arduino UNO Q product/security support for a written,
versioned custom-OS contract containing the exact board/SKU and fuse profile;
authorized root/intermediate public certificate chain or signing service;
signed-manifest schema and canonicalization; anti-rollback index ownership;
partition map and atomic recovery/rollback procedure; signed hashes for a
preserved factory bundle; and explicit binary licence/redistribution terms.
Verify that package offline against an independently authenticated Arduino key
before any board mutation. Until then, the official factory Debian recovery
path remains supportable but cannot satisfy the SimpleOS acceptance row.

Primary sources:

- [Arduino UNO Q user manual](https://github.com/arduino/docs-content/blob/main/content/hardware/02.uno/boards/uno-q/tutorials/01.user-manual/content.md)
- [Arduino UNO Q recipe and rescue hash](https://github.com/arduino/arduino-deb-images/blob/e7713f1797945296e4ab77dc7040b5d2c32aa047/debos-recipes/qualcomm-linux-debian-flash.yaml#L195-L219)
- [Arduino image-recipe BSD-3-Clause licence](https://github.com/arduino/arduino-deb-images/blob/e7713f1797945296e4ab77dc7040b5d2c32aa047/LICENSE.txt)
- [Arduino Flasher registry/checksum validation](https://github.com/arduino/arduino-flasher-cli/blob/68c641ce1d71cb245b8fc2f242376d5e5e65a1d9/internal/registry/http_client.go)
- [Arduino Flasher EDL/QDL transaction](https://github.com/arduino/arduino-flasher-cli/blob/68c641ce1d71cb245b8fc2f242376d5e5e65a1d9/internal/updater/flasher.go)
- [Arduino Flasher GPL licence](https://github.com/arduino/arduino-flasher-cli/blob/68c641ce1d71cb245b8fc2f242376d5e5e65a1d9/LICENSE)
- [Qualcomm QRB2210 data sheet](https://docs.qualcomm.com/doc/80-30843-1/80-30843-1.pdf)
