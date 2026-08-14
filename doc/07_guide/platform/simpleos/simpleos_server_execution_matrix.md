# SimpleOS ARM64 and UNO Q server execution

## Status

The execution matrix is under active implementation and has no production
PASS. ARM source now contains the filesystem payload, VirtIO-MMIO NIC queue,
bounded user-copy/direct socket dispatch, FAT32 metadata-sync, and VirtIO block
FLUSH prerequisites. The latest mandatory preflight confirms both the 5 GiB
storage floor and QEMU executable. The ARM sysroot/runtime, filesystem payload,
RecoverableReplaceV1 source, and provisioned-descriptor capability projection
now exist. The structural projection validates the exact SARD bytes and does
not replace the production mount/recovery-published truth. Live execution is
still blocked by the missing current-source Stage-4/full compiler and matching
server admission receipt. The connected UNO Q still boots Debian and has neither
the physical SimpleOS runtime/provider nor a filesystem server executable.

## Required operator flow

1. Build from current source and retain the source revision and executable hash.
   Record the credential-bearing image SHA-256 for provenance; the hash may be
   retained, but the image itself is never public/distributable evidence.
   Supply `SIMPLEOS_SERVER_DB_CREDENTIAL_FILE` as a non-empty file of at most
   128 bytes; the image stages it as `/SYS/SRVDB.KEY` and fails closed if it is
   absent. Do not place the credential bytes on the command line.
   Keep the generated image ephemeral and access-restricted, then securely
   destroy it after the same-image reboot probe. Exclude it from caches,
   uploads, release artifacts, and evidence bundles.
2. Boot the target through its canonical firmware/image path.
3. List and resolve the server executable from the target filesystem.
4. Probe HTTP health and a filesystem document from the host.
5. Write/read a DB value, stop the target, restart against the same media, and
   read the committed value again.
6. On UNO Q, run once with GPU unselected, then separately require the physical
   Adreno/Vulkan device, submit, completion/fence and device-origin readback
   while an HTTP probe proves the parent server remains live.
7. Emit `SimpleOsServerExecutionReceiptV1` and retain raw transcripts, with
   database credential bytes excluded/redacted from receipts, logs, and protocol
   evidence.

The host image builder wipes its transient credential input buffer after copying
it into the image. The current target runtime cannot guarantee secure zeroing of
the immutable `[u8]` and `text` credential copies after policy registration;
this remains an explicit blocker tracked in
`doc/08_tracking/bug/simpleos_server_credential_zeroization_gap_2026-08-14.md`.

Missing media, runtime, provider, driver, receipt field, or target identity is
a failed/blocked row. Do not use a marker, host service, x86 guest, Debian
process or software GPU as fallback evidence.

## Ownership and optional acceleration

The parent exclusively owns mutable server, database and filesystem state.
CPU/GPU workers receive immutable or generation-bound input and return a
bounded pointer-free result. The parent validates generation, completion,
length and checksum before commit. GPU libraries are selected through the
optional backend owner only; CPU-only execution must not load them.

See `.spipe/simpleos_server_execution_matrix/state.md` for exact acceptance
criteria and `doc/03_plan/agent_tasks/simpleos_server_execution_matrix.md` for
lane ownership and resume commands.

The executable matrix is
`test/03_system/os/server/simpleos_server_execution_matrix_spec.spl`; its
authored mirror is
`doc/06_spec/03_system/os/server/simpleos_server_execution_matrix_spec.md`.
All missing live helpers fail explicitly and every ARM, UNO, and Linux row
remains uncredited. SPipe/docgen and runtime execution have not been run because
the current-source Stage-4 compiler/admission blocker remains; do not describe
the authored mirror as generated evidence.
