# NFR: UP Squared Apollo Lake Intel DCI debug and provisioning

Date: 2026-08-21
Selection: Safety baseline and evidence levels confirmed with A + B + D.

- **NFR-001 — Fail closed:** Unknown target, cable, firmware, memory range,
  descriptor, payload, or storage identity produces BLOCKED/FAIL before mutation.
- **NFR-002 — Authenticity:** Intel proprietary tooling is installed only from
  Intel's authenticated distribution. Payloads and receipts are SHA-256 bound.
- **NFR-003 — Confidentiality:** DCI testing uses a physically controlled,
  secret-free lab target; debug consent is disabled after the session.
- **NFR-004 — Atomicity:** Mailbox commit is the final write and includes a
  generation plus nonce; partial, stale, replayed, or torn descriptors fail.
- **NFR-005 — Bounds:** Integer overflow, segment overlap, address wrap, file
  truncation, `p_filesz > p_memsz`, and non-allowlisted target ranges fail.
- **NFR-006 — Recovery:** The operator retains physical reset and SPI recovery
  capability. OpenRC warm reset and unqualified firmware flashing are forbidden.
- **NFR-007 — Evidence:** Connection, RAM-load, boot, and storage are separate
  receipts; no weaker level promotes a stronger level to PASS.
- **NFR-008 — Portability:** Protocol parsing and policy live in pure Simple;
  Intel-tool interaction and UEFI/storage hardware remain behind capability
  boundaries so another admitted transport can reuse the target logic.
- **NFR-009 — Performance:** Descriptor validation is linear in program-header
  count; payload hashing and copying are linear in admitted bytes with no
  repeated full-image scan after commit.
- **NFR-010 — Auditability:** Every mutation records target identity, operation,
  address or LBA bounds, payload hash, tool/build provenance, and result.
- **NFR-011 — Debug honesty:** The free RSP monitor advertises only implemented
  packet size and bounded RAM operations. Missing register and run-control
  capabilities return the standard empty unsupported response, never fabricated
  state or a false halt/reset result.
- **NFR-012 — Reproducible deployment image:** Identical admitted kernel,
  resident loader, fallback, epoch, and geometry inputs shall produce a
  byte-identical GPT/FAT32 image. The builder pins GPT identifiers, FAT volume
  identity, and timestamps; a two-build fresh-directory gate compares the full
  image and retained components before a hash may be used for media admission.
