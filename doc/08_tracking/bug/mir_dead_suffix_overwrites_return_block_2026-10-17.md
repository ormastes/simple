# MIR dead suffix overwrites an explicit return block

Status: source fix reviewed; dynamic verification UNRUN. No runner or full-suite PASS.

The Cranelift runner with SHA-256
`cb821acf366b792696210a1d108a1aa1ea9a01cbc2a9f84de3e6bc7d53e6a160`
crashes during startup at `run_tests+16540`, dereferencing null `config.session_debug`
with `ldr x6, [x6, #160]`. The configuration return is already zero; this is
not an `updated_options` value-copy fault or an address-space-limit failure.

`load_test_config_from_path` initializes `config` with `TestConfig.defaults()`
and returns it unconditionally before a dead parsing suffix. Native disassembly
contains neither initialization nor that return. It starts with the suffix's
empty-path conditional and returns an uninitialized stack slot (`sp+0x200`).

## Cause and fix

`MirLowering.lower_block_expected` continued lowering statements and the tail
after `lower_return_expr` completed the current block. A later conditional
finalized that same block: `MirBuilder.finalize_block` replaced its instruction
list, and `set_terminator` replaced its return. The live initializer disappeared
while uses of its local remained in the dead suffix.

After each lowered statement, stop this block when the existing
`current_block_has_explicit_terminator()` predicate is true. Return no trailing
value, retaining the explicit terminator and its operand initialization. A
conditional return still leaves its reachable join available, so sibling paths
continue lowering. The fix does not change builder finalization, add builder
state, or rewrite the runner's configuration policy.

The predicate uses the existing block lookup. Calling it on `self.builder`
directly avoids a new builder value binding/copy. It adds one block lookup per
lowered statement; compiler performance has not been measured in this patch.

## Regression evidence

- `test/01_unit/compiler/mir/logical_short_circuit_lowering_spec.spl` compares
  actual serialized MIR for live-only functions against the same functions
  followed by dead conditionals/tails. Cases cover scalar return initialization,
  struct constructor calls, a reachable sibling path, and a void return.
- `test/fixtures/compiler/native_early_return_dead_suffix.spl` must compile and
  execute through both Cranelift and LLVM, exit zero, and print
  `early-return-dead-suffix: PASS`. It checks both boolean branches and reads the
  returned struct's fields, reproducing the original invalid-return hazard.
- Diagnostic artifacts are under
  `/home/yoon/dev/phase3-whole-tests-evidence-20261013/runner-positive-smoke-20261017/`:
  `gdb-startup-registers-disassembly.log`, `run-tests-static-disassembly.log`, and
  `test-config-static-disassembly.log`. The structured diagnosis is
  `runner-startup-segv-diagnosis-20261017.json` in the parent evidence directory.

## Remaining validation

The patch is based on clean release commit
`3c9ec658e68f9c35ae343be54bbcb8c721027ee2` in a private worktree. Root source
review accepted the narrow patch. No updated compiler was built: the captured
`1dfe` compiler cannot prove behavior of compiler source modified afterward,
and its capture receipts alone do not establish execution admission.

With an admitted compiler containing this fix, run the MIR spec once, then
native-build the standalone fixture separately with `--backend cranelift` and
`--backend llvm`, isolated output/cache/runtime authority, and execute each
result. Only after those pass should the runner positive/negative qualification
and authorized Phase 3 suites resume. Compiler/lib/MCP checks, MCP native smoke,
and whole-suite verification remain UNRUN; this source repair is not release
readiness or evidence that either backend passes the whole suites.
