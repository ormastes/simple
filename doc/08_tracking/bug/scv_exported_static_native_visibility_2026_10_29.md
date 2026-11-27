# SCV exported statics require public native declarations

Status: focused native visibility and instrumented bounds checks verified;
production runner and the earlier probe discrepancy remain OPEN.

The corrected BuildRunner manager build passed all 307 MIR and AOP modules,
then failed native compilation in `lib.scv.alloc_bounds`. The recovered P2
producer rejected the imported `ARENA_CONTEXT_CRITICAL_MASK` as a non-public
module static requiring visibility-preserving accessor support. No manager
artifact was published. The declaration already appears in the owner's export
list; making that intended API declaration public does not expose an internal
constant. `DOMAIN_ARENA_U64_MAX` remains private.

A two-module native reproducer distinguishes the declaration visibility from
the export list: private `const` plus explicit export fails with the same
diagnostic, while `pub const` plus the same export builds and executes with
exit 0, checking that the imported value is 62.

- Producer SHA-256: `0d6f2e4720845195c9f91de292056fac4c57cabef81390507c78d95e51133a28`.
- Red log: `/private/tmp/lunar-buildrunner-manager-20261029/native-const-private-export.log`, SHA-256 `c18045b6851c2a542aa6ff5792b5a8a891181f320de6c085d2b338f96bab5891`.
- Green log: `native-const-pub-export.log` in the same directory, SHA-256 `2017fae326586562dbd2c3bf142e07b3f8babcdfcbbb548c747acde6b7bcc3ab`.
- Green native binary SHA-256: `ac3ab16b931a55403958d11163ab9b196183f320bab3c9445e947d061136087c`.

The source correction marks existing exported scalar APIs public in the
arena, allocation bounds, delta, and source-inventory modules. Values and
export lists are unchanged. This is a compatibility correction for the frozen
producer, not a generalized compiler fix for explicit exports.

The first real `scv_bound_object_bytes` native probe compiled successfully
(nine modules) but exited 2 at its above-bound error-prefix assertion. That
is not a behavior pass. The below-bound call and above-bound returned text
were inspected in the expanded probe described below. The original failure
remains unexplained, and the production quota check remains unchanged.

- Real probe build log SHA-256: `5bd95c10853417c0c2edea6109d88b316c6c3fb58acf9b7bacc2e8528f5601a8`.
- Real probe binary SHA-256: `35b8f27b234fff3c6947a1f81485de02901a63abc78946913037d9fc7e59a2bf`.

Darwin strict process ownership, kernel memory enforcement, and full production
BuildRunner Hello remain separate unmet gates. No diagnostic probe substitutes
for them.

The existing arena SSpecs were also attempted through the explicit hosted Rust
seed diagnostic route. V1 reported 11 passed and 3 failed, including a
`File name too long` scenario-artifact failure; V2 reported 0 passed and 1
failed without a detailed cause. No baseline comparison establishes whether
these are pre-existing failures. They are retained as failed checks, not
waived or counted as library qualification.

The expanded instrumented production probe subsequently built and ran with
exit 0. It checked imported object bound 268435456, domain ID 7, delta depth
10, inventory schema 1, and inventory maximum 268435456. Request 17 returned
empty text (length 0); imported maximum plus one returned the expected error
prefix (length 104). All assertions passed and it printed `SCV_BOUNDS_OK`.

- Expanded build log SHA-256: `9faf2b679b667a936aeb48cddee5ef40424a3e7341584c2b2c7fd9ad746b5ed9`.
- Expanded artifact SHA-256: `8a7c1f445649567d66b066b9fbaaea42cc0739635fa659e95c06f31605a63400`.

The earlier run-2 discrepancy has not been explained: the expanded probe adds
imports and instrumentation and computes the above-bound request from the
imported maximum. Do not claim a diagnosed runtime/compiler repair from that
change. The five native values are verified; other qualifiers consistently
mark the same existing exported API surface. Not every exported value had an
existing external consumer.
