# TCM1 active toolchain release manifest

`src/os/kernel/loader/toolchain_active_release_manifest_tcm1.spl` defines a
package-private, data-only TCM1 codec. It makes no filesystem calls and grants
no execution or catalog authority.

TCM1 has exactly 17 ordered slots: the three Simple SMFs, the nine
Clang/sysroot entries, then the five primary-tool entries. Payload and SCR1
paths are loader constants and are omitted from the wire format; decoding
reconstructs them by index. This eliminates aliases, traversal strings, and
caller-selected paths at the parsing boundary.

The manifest binds a lowercase, nonzero 64-hex release identifier to a
supported SimpleOS target, lowercase signer key identifier, lowercase 64-hex
root digest, and each slot's payload/SCR1 digest plus positive bounded sizes.
The aggregate is capped at 512 MiB. Decode accepts only the canonical TCM1
encoding with no trailing bytes and returns a newly reconstructed value, not a
view of caller-owned wire storage.

It is intentionally not wired into image building, boot selection, legacy
media handling, signature verification, or catalog mutation yet.
