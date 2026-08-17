# Deployed Simple checker crashes on StarFive implementation files

Status: PARTIALLY FIXED / host source fixed; redeployed x86_64 and physical JH7110 evidence pending

- Date: 2026-08-15
- Command: `bin/simple check src/lib/nogc_async_mut/fs_driver/ramfs.spl ...`
- Executable: `/home/yoon/simple/release/x86_64-unknown-linux-gnu/simple`
- SHA-256: `04a38e21d6fbd86149d46d3ee2d761349f8ad29b02c5037a8eb589b6a1b9e4e0`
- Result: exit 139 while checking the first file, before any source diagnostic.

This reproduces the already-known deployed self-host environment-write/miscompile class referenced by `scripts/lib/simple-compiler-select.shs`. It blocks running the generated SSpec through the deployed full CLI. It no longer blocks the board build or physical acceptance: a provenance-admitted pure-Simple Stage 3 compiler builds the ELF, and the canonical contract/self-test/live checker passes. Do not use the Rust seed as a substitute for repairing the deployed full CLI.

---

## Host audit 2026-08-17

The recorded executable path is an **x86_64 Linux host runtime**, not a binary
running on the StarFive board. The earlier RISC-V-hardware classification was
incorrect. On the current x86_64 host the historical SHA-256 artifact is not
present, so the exact exit-139 artifact cannot be replayed. Invoking the release
wrapper instead fails closed at its bounded identity probe because no deployed
x86_64 runtime is installed; it does not reproduce the crash.

The source tree contains the scalar HIR metadata transport repair used by the
Stage 3 exit-139 investigation: array-literal lowering calls
`copy_local_hir_type_metadata`, whose implementation rejects nil and staged
raw-zero sentinels. The release wrapper now also refuses recursive delegation
instead of silently executing the Rust bootstrap seed. The adjacent regression
in `compile_delegation_wrapper_loop_spec.spl` pins that pure-Simple-only
acceptance invariant.

Remaining evidence is deliberately split:

- Rebuild and deploy an x86_64 pure-Simple runtime, record its provenance, and
  rerun the original `check` command to close the host crash report.
- Run the canonical live checker on physical JH7110 hardware to close the
  board acceptance gate. Host success must not be presented as device evidence.
