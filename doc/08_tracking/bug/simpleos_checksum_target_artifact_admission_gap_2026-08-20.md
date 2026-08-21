# SimpleOS checksum target artifact admission gap

Status: BLOCKED

`sha256sum` and `md5sum` have real bounded pure-Simple implementations and now
have canonical filesystem artifact identities at `/usr/bin/sha256sum` and
`/usr/bin/md5sum`. The shell no longer executes either utility as a builtin.

Execution remains blocked because no target-native artifact digest and no
loader-owned, target-bound executable authority token are available to the
launcher. The launcher returns exit code 126 and does not call the legacy spawn
path. Source presence, package declarations, version text, and digest output
must not be used as substitute admission evidence.

Closure requires all of the following for x86_64, AArch64, and RISC-V 64:

- target-native checksum artifacts built from the declared pure-Simple owner;
- package identities bound to exact artifact digests;
- cryptographic executable admission and a loader-owned consume-once token;
- a launcher recipe that delegates bounded `FileRead` authority for the exact
  operands without granting ambient filesystem access;
- FAT32, DBFS, and NVFS launch-and-hash evidence covering the documented input
  bounds, exact help/version behavior, missing files, and unsupported options.
