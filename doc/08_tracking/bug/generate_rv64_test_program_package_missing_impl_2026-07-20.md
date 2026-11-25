# Missing implementation: src/hardware/fpga_linux/generate_rv64_test_program_package.spl

- **Status:** RESOLVED 2026-11-25 — the generator exists and its output matches
  every spec assertion byte-for-byte (see "Verification 2026-11-25" below).
  (Was: OPEN — filed 2026-07-20 when the file did not exist; it was added by
  commit `caed58386e5` "fix(fpga): add generate_rv64_test_program_package
  emitter for rv64 test program pkg".)
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

## Verification 2026-11-25 (release/1.0.0, Windows lane)

`src/hardware/fpga_linux/generate_rv64_test_program_package.spl` now exists
(added by `caed58386e5`) and was exercised directly with the spec's exact
fixture (9-byte firmware `\x01..\x09`, 4-byte payload `\xAA\xBB\xCC\xDD`):

```
SIMPLE_LIB=src bin/simple.exe run src/hardware/fpga_linux/generate_rv64_test_program_package.spl \
  -- fw.bin fw.hex payload.bin payload.hex test_program.vhd    # rc=0
```

Outputs match every assertion in
`test/01_unit/hardware/fpga_linux/generate_rv64_test_program_package_spec.spl`
byte-for-byte:

- `fw.hex` == `0807060504030201\n0000000000000009\n` (exact)
- `payload.hex` == `00000000DDCCBBAA\n` (exact)
- the `.vhd` contains all asserted constants: `HEX_WORD_BYTES := 8`,
  `FW_SIZE_BYTES := 9`, `FW_HEX_PATH`, `PAYLOAD_SIZE_BYTES := 4`,
  `PAYLOAD_HEX_PATH`, `FW_BYTES : byte_array_t(0 to 8)` with rows
  `        x"01",` ... `        x"09"\n    );`, and
  `PAYLOAD_BYTES : byte_array_t(0 to 3)` with `        x"AA",` ...
  `        x"DD"\n    );`

Limit: the spec itself could not be executed through `bin/simple.exe test`
because release/1.0.0 HEAD carries `@representation_boundary` annotations
(commit cfd89933699) that the pinned seed rejects repo-wide; the generator was
therefore run directly and its outputs compared against the spec's literal
oracles by hand. The generator's own run is unaffected (rc=0, no decorator in
its import closure).

The secondary issue noted above (`bin/simple run` exiting 0 on a missing entry
file) is a separate CLI-behavior question and was not re-tested here; it does
not affect this bug's closure, which is about the missing generator.
