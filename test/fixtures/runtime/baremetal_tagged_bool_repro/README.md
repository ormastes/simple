# Baremetal tagged-boolean C ABI reproducer

This diagnostic links each **complete real production translation unit** and executes its reachable helpers in a freestanding static ELF under Linux QEMU user mode. No owner definitions are copied, extracted, mocked, or patched. It reproduces the consumer defect tracked by PR #7319, independently of the previously fixed producer constants.

## Run

Requirements: Linux, clang with x86_64/AArch64 backends, lld, GNU timeout, sha256sum, Git, tar, qemu-x86_64 and qemu-aarch64. The output directory must not exist. `CC`, `QEMU_X86_64` and `QEMU_AARCH64` each select one executable, without embedded arguments.

```sh
sh test/fixtures/runtime/baremetal_tagged_bool_repro/run.shs x86_64 /tmp/bool-x86-fresh
sh test/fixtures/runtime/baremetal_tagged_bool_repro/run.shs arm64 /tmp/bool-arm-fresh
# Every run archives committed sources; the optional third argument selects the revision:
sh test/fixtures/runtime/baremetal_tagged_bool_repro/run.shs arm64 /tmp/bool-candidate-fresh 41fb5530ad3d49924f560a86abe29544a42cb4f5
```

Each command returns the actual fixture status: **0 means all 190 assertions pass; 1 means semantic failure; 124 means execution timed out.** Build/tool errors are errors, not test passes. `result.log` lists failing operations, case indices and observed/expected ABI values. Artifacts, compile logs, source identity, runner, source-archive, binary, compiler, linker and emulator digests remain in the output directory. This diagnostic intentionally fails on the recorded current release; do not invert that failure into a release PASS or add a blanket CI exemption.

## Original and similar cases

The first assertion calls the actual `rt_not(19)` and requires tagged true (11). Nine inputs cover both tagged booleans, encoded integer zero/one/two/negative one, nil, and both signed encoded-integer extremes. Every input checks negation, conversion and boolean recognition; all 81 ordered pairs check conjunction and disjunction. The `rt_is_bool` oracle preserves its existing raw 0/1 return ABI. Oracles are explicit ABI values, independent of production macros.

The corresponding candidate in #7319 passes the same assertions. That positive control detects regressions in these primitive C ABI cases, including operand-order asymmetry, accidentally treating integers as booleans, losing the tagged-true conversion, and incorrect nil/integer truthiness. It does **not** cover heap conversion branches or claim unit-owner branch coverage.

## Limits

Linux syscall startup and QEMU user mode are a fixture host, **not** baremetal startup, QEMU system/device boot, or an admitted Simple-generated caller. Whole-TU compilation checks the real owner, while section garbage collection deliberately removes unrelated entrypoints and device services. This is faithful evidence for the primitive C ABI boundary only. The original Simple-to-runtime/system acceptance, compiler/lib/MCP checks and bug-fix admission remain incomplete. Production source and bug closure status are unchanged by this test-only addition.

See [retained results](../../../../doc/09_report/baremetal_tagged_bool_reproduction_20261107.md).
