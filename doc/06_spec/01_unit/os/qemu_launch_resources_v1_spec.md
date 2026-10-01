# QEMU guest launch resources

**Manual draft; execution and SPipe regeneration TEST_BLOCKED.**
Source: `test/01_unit/os/qemu_launch_resources_v1_spec.spl`.
Requirements: platform unification REQ-014 and REQ-022.

1. Normalize `32G`, `512m` and a plain MiB value. Expect 32768, 512 and the
   unchanged MiB count, respectively.
2. Reject empty, negative, malformed and oversized memory values. Expect the
   invalid sentinel zero, which machine-plan admission rejects.
3. Read CPU counts 1, 10 and 4096. Reject zero, negative, fractional and
   oversized values before any narrowing to the u16 plan field.

The runtime scenarios use real parsing functions and concrete assertions. They
have not executed in this checkout. No capture or generated zero-stub receipt
exists yet. Resume with the admitted Stage 4 commands in
`doc/03_plan/sys_test/simpleos_sealed_cli_dispatch.md`.
