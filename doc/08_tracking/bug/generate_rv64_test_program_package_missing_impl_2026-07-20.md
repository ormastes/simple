# Missing implementation: src/hardware/fpga_linux/generate_rv64_test_program_package.spl

- **Status:** OPEN
- **Discovered:** 2026-07-20, whole-suite triage campaign
- **Area:** `src/hardware/fpga_linux/` — RV64 FPGA test-program VHDL package
  generator
- **Severity:** Medium — the only consumer (its own spec) can never pass;
  the tool this spec describes does not exist anywhere in the repo.

## Symptom

`test/unit/hardware/fpga_linux/generate_rv64_test_program_package_spec.spl`,
example "emits 64-bit preload rows and keeps byte-array metadata coherent",
fails:

```
✗ emits 64-bit preload rows and keeps byte-array metadata coherent
    expected  to contain         x"DD"
    );
```

(`pkg_text` — the content read back from the generated `.vhd` file — is
empty, because the generator never wrote it.)

## Root cause

The spec's `it` block shells out to:

```
bin/simple run src/hardware/fpga_linux/generate_rv64_test_program_package.spl -- <fw_bin> <fw_hex> <payload_bin> <payload_hex> <pkg>
```

but `src/hardware/fpga_linux/generate_rv64_test_program_package.spl` does
**not exist** in the working tree or anywhere in git history (`git log --all
-- <path>` returns no hits when checked directly with `git cat-file -e` at
the commits that superficially matched a pathspec log search; the file was
never actually committed). Manually re-running the exact `bin/simple run`
invocation confirms:

```
error: compile failed: io: Cannot read "src/hardware/fpga_linux/generate_rv64_test_program_package.spl": No such file or directory (os error 2)
```

`shell(...)` in the spec only checks the exit code of `bin/simple run`
(which is `0` even on this internal compile-failure path — a related but
separate minor issue: the compiler prints `error: compile failed: ...` to
stdout/stderr yet the wrapping process exits `0`), so the spec proceeds past
the `expect(shell(...)).to_equal(0)` assertion and only fails later when it
tries to read the (nonexistent) generated `.vhd` file, yielding an empty
string that then fails the `to_contain` checks.

The neighboring `generate_riscv_fpga_bundle.spl` in the same directory is a
**different** tool (RISC-V FPGA RTL bundle generator, board/product-level
CLI flags) — not a renamed/refactored successor of the missing
byte-preload-package generator, so this is not a simple rename fix. No
`HEX_WORD_BYTES`/`byte_array_t`/`PAYLOAD_HEX_PATH`-shaped generator logic
exists anywhere under `src/` (grepped repo-wide).

## Failing command

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 \
  /home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple \
  test test/unit/hardware/fpga_linux/generate_rv64_test_program_package_spec.spl --no-session-daemon
```

## Recommendation

Either (a) implement
`src/hardware/fpga_linux/generate_rv64_test_program_package.spl` per the
spec's expectations (reads `fw_bin`/`payload_bin`, emits `fw_hex`/
`payload_hex` as big-endian hex-word text files, and emits a VHDL package
`.vhd` with `HEX_WORD_BYTES`/`FW_SIZE_BYTES`/`FW_HEX_PATH`/
`PAYLOAD_SIZE_BYTES`/`PAYLOAD_HEX_PATH`/`FW_BYTES`/`PAYLOAD_BYTES`
constants matching the spec's literal assertions), or (b) if this tool was
superseded/descoped, remove the dead spec — but per triage rules that
decision is for the feature owner, not this pass; the spec's assertions are
legitimate and were not weakened here. Secondary, smaller issue worth fixing
alongside: `bin/simple run` on an unreadable/missing entry file exits `0`
despite printing `error: compile failed: ...` — callers that check only the
exit code (like this spec's `shell()` helper) silently proceed past a real
compile failure.
