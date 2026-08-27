# RV64 Serial Management Shell Specification

> Verifies the UART telnet/ssh-over-serial management fallback used when the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Serial Management Shell Specification

Verifies the UART telnet/ssh-over-serial management fallback used when the

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | riscv64-fpga-simpleos |
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/os/kernel/arch/riscv64/shell_lite_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies the UART telnet/ssh-over-serial management fallback used when the
FPGA/board has no working network. Tests the pure command dispatch: a given
input line must produce the expected response, so a broken shell fails here.

## Scenarios

### rv64 serial shell dispatch

#### help lists the commands

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- help lists the commands
   - Expected: rv64_shell_dispatch("help", 0) equals `rv64_shell_help()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("help lists the commands")
expect(rv64_shell_dispatch("help", 0)).to_equal(rv64_shell_help())
```

</details>

#### echo returns its argument

- echo returns its argument
   - Expected: rv64_shell_dispatch("echo hello world", 0) equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("echo returns its argument")
expect(rv64_shell_dispatch("echo hello world", 0)).to_equal("hello world")
```

</details>

#### net reports unavailable when network is down

- net reports unavailable when network is down
   - Expected: rv64_shell_dispatch("net", 0) equals `network: unavailable - UART telnet/ssh fallback in use`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("net reports unavailable when network is down")
expect(rv64_shell_dispatch("net", 0)).to_equal("network: unavailable - UART telnet/ssh fallback in use")
```

</details>

#### net reports ready when network is up

- net reports ready when network is up
   - Expected: rv64_shell_dispatch("net", 1) equals `network: ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("net reports ready when network is up")
expect(rv64_shell_dispatch("net", 1)).to_equal("network: ready")
```

</details>

#### info identifies the rv64 serial console

- info identifies the rv64 serial console
   - Expected: rv64_shell_dispatch("info", 0) equals `SimpleOS RV64 (riscv64) - serial console fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("info identifies the rv64 serial console")
expect(rv64_shell_dispatch("info", 0)).to_equal("SimpleOS RV64 (riscv64) - serial console fallback")
```

</details>

#### pwd reports the root directory

- pwd reports the root directory
   - Expected: rv64_shell_dispatch("pwd", 0) equals `/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pwd reports the root directory")
expect(rv64_shell_dispatch("pwd", 0)).to_equal("/")
```

</details>

#### ls is intercepted by the console (not pure dispatch), so dispatch reports it unknown

- ls is intercepted by the console (not pure dispatch), so dispatch reports it unknown
   - Expected: rv64_shell_dispatch("ls", 0) equals `unknown command: ls\r\nType 'help' for commands.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ls is intercepted by the console (not pure dispatch), so dispatch reports it unknown")
# `ls` needs the VFS and is handled in console.spl before dispatch;
# pure dispatch therefore reports it as unknown. The real listing is
# verified end-to-end by the QEMU boot (boot->login->ls->file listing).
expect(rv64_shell_dispatch("ls", 0)).to_equal("unknown command: ls\r\nType 'help' for commands.")
```

</details>

#### reboot acknowledges

- reboot acknowledges
   - Expected: rv64_shell_dispatch("reboot", 0) equals `rebooting...`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reboot acknowledges")
expect(rv64_shell_dispatch("reboot", 0)).to_equal("rebooting...")
```

</details>

#### unknown command is reported, not silently dropped

- unknown command is reported, not silently dropped
   - Expected: rv64_shell_dispatch("frobnicate", 0) equals `unknown command: frobnicate\r\nType 'help' for commands.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unknown command is reported, not silently dropped")
expect(rv64_shell_dispatch("frobnicate", 0)).to_equal("unknown command: frobnicate\r\nType 'help' for commands.")
```

</details>

#### empty line yields empty response

- empty line yields empty response
   - Expected: rv64_shell_dispatch("", 0) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty line yields empty response")
expect(rv64_shell_dispatch("", 0)).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e737501efabc28766473e26492fdee38a59cd10d135e5d55f4162f2cbc3b4703`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e737501efabc28766473e26492fdee38a59cd10d135e5d55f4162f2cbc3b4703`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e737501efabc28766473e26492fdee38a59cd10d135e5d55f4162f2cbc3b4703`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/kernel/arch/riscv64/shell_lite_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/arch/riscv64/shell_lite_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/arch/riscv64/shell_lite_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/arch/riscv64/shell_lite_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/arch/riscv64/shell_lite_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'help lists the commands' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/arch/riscv64/shell_lite_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'echo returns its argument' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/arch/riscv64/shell_lite_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'net reports unavailable when network is down' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
