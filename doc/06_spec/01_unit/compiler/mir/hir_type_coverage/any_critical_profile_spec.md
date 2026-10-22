# Actual MIR Any profile enforcement

Requirement: REQ-MC-ANY-001. Status: AUTHORED / UNRUN.
Source: `test/01_unit/compiler/mir/hir_type_coverage/any_critical_profile_spec.spl`.
Manual authored directly; qualified runner and docgen execution remain UNRUN.

Run this spec in an isolated process because it temporarily changes
`SIMPLE_SAFETY_PROFILE`. Each operation restores the exact nullable previous value
before assertions. No source substring is accepted as evidence of rejection.

| Step | Independent expected result |
|---|---|
| Lower a typed Any through actual `MirLowering.lower_type` | I64 recovery type plus exactly one E-MIR-TYPE-Any diagnostic |
| Select critical, mission-critical, or verified | Fatal flag and actual driver rejection classifier are true |
| Select robust, strict, moderate, or empty | Fatal flag and driver rejection classifier are false |
| Inspect the diagnostic span | Bytes 21–24, line 3, column 9 |
| Parse/lower a complete function with an Any parameter | Critical/alias reject; robust retains the existing nonfatal diagnostic |
| Replace its parameter with i64 | No MIR errors |

The I64 recovery value does not mean compilation is permitted: the driver
classifier is checked separately. Runtime execution and broader CLI profile/hash
parity remain unqualified; this manual claims neither.
