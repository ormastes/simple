# Kernel qualification profile metadata

Status: **AUTHORED_UNRUN**; manual mirror, not generated docgen or native evidence.
Source: `test/01_unit/lib/common/contracts/container/kernel_qualification_v1_spec.spl`.

1. **Encode exact policy fields without assuming a SHA256 build ID.** Compare
   the codec with independently supplied canonical fields; accept GNU note IDs
   from one through 64 bytes, preserving their exact lowercase encoding.
2. **Reject odd uppercase oversized and nonhex GNU note identities.** Reject
   release paths, controls, non-ASCII and oversize strings before observation.
3. **Decode only the frozen metadata schema.** Unknown authority flags, wrong
   scalar types, duplicate fields and noncanonical wire bytes refuse.
4. **Keep source config patch and rule provenance distinct.** Each installed
   manifest/identity changes the canonical digest. Unsupported rules and
   malformed manifest hashes refuse.

A valid codec result is configuration data only. No test constructs installed
Host authority, a native kernel owner, a terminal receipt or capacity discharge.
All four scenarios are unexecuted; compiler/library/MCP qualification and docgen
remain pending.
