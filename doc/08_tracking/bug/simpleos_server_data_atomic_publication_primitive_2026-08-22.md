# SimpleOS server-data image needs a bounded atomic publication primitive

## Blocked acceptance

The pure-Simple server-data DBFS image provisioner cannot yet publish a 32--256
MiB binary image with the required bounded-memory, private-temp, durable,
atomic-no-clobber contract.

## Evidence

- `rt_file_create_excl(path, content)` takes whole `text` content and creates
  the final path before completing its write. Readers can observe partial data;
  converting a 256 MiB byte image to text also adds an unbounded whole-image
  copy and has no proven arbitrary-binary contract.
- `file_rename`/`rt_file_move` overwrite an existing destination and therefore
  cannot implement no-clobber publication.
- `file_fsync` in the current Simple facade only checks existence. There is no
  parent-directory fsync facade.
- `AsyncFile` provides exclusive open, positioned writes, and file fsync, but
  exposes no hard-link or rename-no-replace publication operation.
- The credential image flow uses shell `mktemp` + `ln` around the FAT-specific C
  writer. It is not a callable Pure-Simple DBFS artifact facade and has no
  portable descriptor/parent-directory durability receipt.
- `MemBlockDevice` allocates the whole image by per-byte push and value-semantic
  sector updates copy its backing array. Combining `bytes()`, byte-to-text,
  reopen, and a second conversion produces several whole-image copies and can
  exceed 1 GiB traffic/RSS at the 256 MiB default.

## Required narrow capability

Add one reviewed host-artifact owner beneath a Pure-Simple facade which:

1. creates an unpredictable same-directory 0600 regular temp without following
   symlinks;
2. supports bounded binary positioned writes plus sparse-safe truncate;
3. fsyncs and reopens the exact descriptor/path for bounded verification;
4. publishes via atomic hard-link or rename-no-replace;
5. fsyncs the parent directory and returns a typed post-publication outcome;
6. cleans only its exact unpublished temp and never removes an existing target.

Until that capability exists, the provisioner must fail closed. Do not use a
shell `ln`, overwrite rename, whole-image text conversion, Rust-seed fallback,
or direct C/Rust DBFS replacement as a workaround.
