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
