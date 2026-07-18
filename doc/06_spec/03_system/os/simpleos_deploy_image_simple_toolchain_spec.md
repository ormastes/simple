# SimpleOS Target Simple Payload Deployment

Source: `test/03_system/os/simpleos_deploy_image_simple_toolchain_spec.spl`

Status: negative/provenance contract implemented; target build and QEMU proof
pending. Stubs: 0.

## Deployment contract

1. Build the full `src/app/cli/main.spl` entry closure for
   `x86_64-unknown-simpleos` with stub fallback disabled.
2. Verify a static target ELF and write its build stamp only after success.
3. Refuse marker files, missing stamps, wrong targets, bootstrap-only entries,
   and wrong ELF architectures before staging starts.
4. Copy the validated payload to `/bin`, `/usr/bin`, and all compiler,
   interpreter, and loader roles; record `/SYS/SIMPLETOOL.SDN` provenance.

## Verification

The executable scenario proves a former `SMF_FAKE_TARGET_SIMPLE` payload now
fails and no toolchain manifest is written. Final acceptance requires a real
payload at every role plus in-guest `simple --version` and hello compile/run.
