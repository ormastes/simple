# UNO Q QRB2210 signed boot/download owner missing

## Status

Blocked on authoritative Arduino/Qualcomm platform inputs. The physical board
must remain read-only; Debian execution receives no SimpleOS credit.

## Gap

SimpleOS has QRB2210 display, input, audio, Vulkan, and evidence-admission
contracts, but no owner for a signed boot bundle, board-specific partition
manifest, anti-rollback metadata, EDL/download transaction, recovery image, or
SimpleOS rootfs carrier. Arduino documents vendor Linux recovery through App Lab
or Flasher CLI and Qualcomm EDL `05c6:9008`, but the reviewed public material
does not define an authorized arbitrary-OS signing or partition procedure.

## Safe closure

Acquire vendor-authoritative signed artifacts and manifests; implement a pure
admission checker first; require explicit destructive authorization plus
`/tmp/unoq-server-matrix.lock` for any later write; verify board/revision,
signatures, rollback index, complete recovery material, and exact payload hashes
before mutation. Use only the vendor-supported flasher and prove a SimpleOS boot
identity before server/GPU evidence. Never guess a partition, use an unofficial
Firehose programmer, unlock/replace the boot chain, or count Debian.

## 2026-08-14 official-source disposition

An official-source-only follow-up found a pinned Arduino factory rescue input,
but not the missing custom-OS authority. Arduino's public image-build recipe
pins `unoq-bootloader-emmc-linux-251020.zip` at SHA-256
`c606e95d0107f8c58d0dd9494e00624d1db7c4361cca20513bc78ef02ca28dd1`, and its
GPL flasher publishes the EDL/QDL recovery transaction. However, `info.json`
and the image checksum travel through the same HTTPS channel; no detached
manifest signature or pinned public trust root is present. Qualcomm documents
QRB2210 secure boot/key provisioning but publishes no UNO Q owner key, fuse
profile, rollback policy, or custom signing service.

The public code licences (BSD-3-Clause for image recipes and GPL-3.0-or-later
for the flasher) do not authorize SimpleOS signing and do not establish the
licence of every binary in the hosted rescue archive. No archive was downloaded
and no board was touched.

**Exact unblock request:** obtain from Arduino product/security support a
written custom-OS contract and independently authenticated signed package that
binds UNO Q SKU/fuse profile, root/intermediate certificates or signing service,
manifest canonicalization, anti-rollback ownership, partition map, recovery and
rollback steps, factory bundle hashes/signatures, and binary redistribution
terms. Continue to fail closed until that package verifies offline.

Evidence:

- https://github.com/arduino/arduino-deb-images/blob/e7713f1797945296e4ab77dc7040b5d2c32aa047/debos-recipes/qualcomm-linux-debian-flash.yaml#L195-L219
- https://github.com/arduino/arduino-flasher-cli/blob/68c641ce1d71cb245b8fc2f242376d5e5e65a1d9/internal/registry/http_client.go
- https://github.com/arduino/arduino-flasher-cli/blob/68c641ce1d71cb245b8fc2f242376d5e5e65a1d9/internal/updater/flasher.go
- https://docs.qualcomm.com/doc/80-30843-1/80-30843-1.pdf
