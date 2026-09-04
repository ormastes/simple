# An `Err(FsError)` payload reads as a zero/default value in freestanding cranelift builds

Title deliberately covers BOTH live hypotheses; they have not been separated yet
and whoever picks this up should not be pointed at one of them prematurely:

- **H1** a `match` over `FsError` selects no arm in this build mode; or
- **H2** the `FsError` payload of an `Err` does not survive transfer out of
  `NvfsDriver.new_on_device` / `unwrap_err()`, so a total match sees a
  zero-initialized value and every arm test fails.

H2 is somewhat favoured: `is_err()` was TRUE (the tag transferred), so the tag
and the payload disagree. A one-run discriminator settles it — construct
`FsError.NotFound` locally inside the round-trip entry, classify it, print the
code. `6` in-guest ⇒ H2; `0` ⇒ H1.

- Date: 2026-09-01
- Status: OPEN — blocks `scripts/check/check-simpleos-nvfs-server-roundtrip-ovmf.shs` at rung L4
- Lane: nvfs (SimpleOS VFS server round-trip, OVMF real firmware)
- Affects: freestanding native builds (`--target x86_64-unknown-none`, `--backend cranelift`,
  `SIMPLE_ALLOW_FREESTANDING_STUBS=1`). Hosted interpreter is CORRECT.

## Symptom

`src/os/kernel/boot/nvfs_root_mount_transaction.spl` classifies the backend error
of a refused root open:

```
val open_err  = opened.unwrap_err()          # Result<NvfsDriver, FsError>
val open_code = _nvfs_boot_fs_error_code_v1(open_err)
```

`_nvfs_boot_fs_error_code_v1` is a total `match` over all 15 `FsError` variants,
returning `1..15`. **Zero is not a value any arm can produce.**

Measured on the real guest, twice, on two different builds:

- with the classifier returning `text` literals:
  `nvfs-root: driver-open-failed:` — the name is the EMPTY string
- with the classifier returning `i64`:
  `nvfs-root: driver-open-failed:code=0:base=4:blocks=8188`

So the match selects no arm and the result is a zero/default value. The integer
interpolations in the same string (`base=4`, `blocks=8188`) are CORRECT, so
string interpolation and integer formatting are fine; the defect is the match
over the enum value (or `unwrap_err()` producing a zero-initialized payload).

## This is not a fabricated stub

`_nvfs_boot_fs_error_code_v1` / `_nvfs_boot_fs_error_name_v1` do **not** appear in
the build's `FABRICATED-NEW` list (135 symbols,
`build/os/nvfsrt/kernel-build.log`). Neither does any DBFS engine symbol on the
open path. The gate's own L11 rung is green, i.e. no load-bearing NVFS symbol was
stubbed. The classifier is really compiled and really called.

## Why it matters beyond diagnosis

`DbFsDriver.open_on_device` and everything beneath it is written in terms of
`Result<_, FsError>` with `match` on the error. If a `match` over `FsError`
cannot select an arm in this build mode, that is a strong candidate for the
CAUSE of the `driver-open-failed` this record was written to diagnose — not
merely for the loss of its message.

## Contrast that isolates it

`test/01_unit/os/port/nvfs_image_boot_open_agreement_spec.spl` runs the WHOLE
boot transaction (superblock select -> DBFS backing validate -> driver open ->
VFS stage -> positioned route -> commit) against the same staged volume, in the
interpreter: **3/3 pass**. Same code, same volume geometry (`base=4`,
`blocks=8188`, confirmed identical by the serial line above). The only variable
is the freestanding native build.

## Reproduce

```sh
cd src/compiler_rust && cargo build --release --bin simple
sh scripts/check/check-simpleos-nvfs-server-roundtrip-ovmf.shs      # FAIL, L4..L10
grep -a 'production mount' build/os/nvfsrt/nvfs_server_roundtrip_ovmf.serial.log
bin/simple test test/01_unit/os/port/nvfs_image_boot_open_agreement_spec.spl  # 3/3 PASS
```

## Not done here

No workaround was applied and the gate was NOT made to pass. Rewriting the
mount path to avoid `match` would hide a compiler defect that affects every
`Result<_, FsError>` consumer in the freestanding kernel, not just this lane.
