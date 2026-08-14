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
