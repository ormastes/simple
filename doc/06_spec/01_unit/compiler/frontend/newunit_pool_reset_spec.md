# Newunit Pool Reset Specification

Source: `test/01_unit/compiler/frontend/newunit_pool_reset_spec.spl`

## Scenarios

1. Register a newunit, reset parser pools for the next file, and verify the
   resulting flat type-pool dump and restore contain no prior newunit name or
   suffix.
2. Register a current-file newunit with backslash and newline characters in
   both text fields. Verify a flat pool dump and restore preserve its name,
   suffix, and underlying type tag.

## Verification status

The focused native harness did not produce an executable: the admitted Stage2
compiler's HIR worker crashed while lowering the harness module. These
scenarios have not been reported as passing. Full Stage2 verification remains
the release gate.
