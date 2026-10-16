# Baked native producer cannot dispatch typed array concat

Date: 2026-10-16. Status: source workaround prepared; DB reconciliation pending;
native verification UNRUN. Recovery base: 1986eb71e4ad1d334d795a4706c2bd06e7a0722b.

The exact0CD6 producer's retained C1 MIR diagnostics contain 95 unresolved
`concat` calls across eight modules. Source matching identifies 89 byte-array
calls, three text-array calls, two AsyncError-array calls and one HirStmt-array
call. These are not all byte arrays. The source compiler dispatch repair cannot
change an already baked bootstrap executable.

The compatibility workaround uses a new pure `std.common.bytes.concat_copy_v1`
owner for byte arrays and three owner-local typed helper families for text,
AsyncError and HirStmt arrays. Each helper allocates fresh output, copies left
then right with typed indexing/push and retains both inputs. No generic helper,
merge/extend, array `+`, FFI, copied mutable state or in-place append is used.
Calls retain original argument evaluation order, field assignments and metadata.
Integer byte literals are explicitly narrowed to their original byte values.

The inverse-rewrite source proof reconstructs every original consumer file,
ignoring only the added tags/imports/helpers and explicit numeric byte casts.
It is evidence of unchanged call arguments and surrounding source, not runtime
qualification. Aggregate repeated-buffer copying remains quadratic as before.

## Verification plan and budget

This remains the same concat feature: at most three verification/fix cycles,
with no budget reset. No build is authorized until complete source review and
an explicit freeze. Existing UI and eligibility budgets are separate and remain
exhausted; this source does not resume them.

`test/01_unit/compiler/bytes_concat_copy_native.spl` has nine explicit nonzero
failure controls covering empty operands, high bytes, left/right order, same
input aliases, result mutation isolation, empty-case fresh storage, chained
calls and original input lengths. It imports the real byte helper without BDD.
Actual stdout, exit status, stderr and a genuine noFORCE link are required.

Actual owner-level record tests remain planned, not executed: construct two
AsyncError values with distinct codes/messages/spans and all help/note/suggestion
fields, append through the owner helper, and assert every field in left/right
order plus unchanged input arrays after output mutation. Construct HirStmt values
with distinct kinds and spans; assert whole nested payloads remain intact. Test
the real statement-lowering prefix/body composition while checking the original
HirBlock has/value/span/unsafe_caps metadata. Test the real reverse-reference
receipt prefix/projection encoding and digest roundtrip. These tests require
genuine owner visibility and larger compiler dependencies; the byte fixture
does not qualify them. Do not widen private APIs solely to simplify tests.

Potential remaining risks include typed native push representation, nominal
record ownership/value copying, module resolution and old-producer field ABI.
The previous record-field bug is a risk to inspect, not proof of failure here.
Full canonical compiler compilation remains required for all 95 production
sites and independent downstream failures. No object/link success is claimed.

## Cycle1 scoped result and cycle2 source preparation

Exact0CD6 real byte helper fixture passed nine controls ONCE: exit0, exact PASS stdout, stderr0B; immutable candidate7524ADDBE599442C7BF896F62ED5556D255A07253AC7F4DDF5F3EDFA0155D297. A missing sparse backend ABI header interrupted public linking; genuine frozen header recovery and fresh38-own-runtime-C/manual strictlink completed cycle1 with retained proofs. No passing byte controls are rerun.

Cycle2 SOURCE ONLY, native UNRUN: the actual async text/AsyncError and HirStmt helpers are moved unchanged into compiler.hir.hir_lowering.concat_copy_v1. Original two consumers import these exact functions, retaining calls and metadata. Three normalized body comparisons are exact. This avoids importing the full lowering engines merely to test concrete copies; there are no mirrored helpers or synthetic records.

New concat_owner_integration_native fixture exercises genuine records and every AsyncError/Span field, nested actual HirStmt/HirExpr/HirType payloads, fresh result/input isolation, actual reverse-reference receipt encode/decode/digest plus denials, and actual launch metadata trailer production byte calls. It reports all five independent group outcomes and returns nonzero if any fails. Explicit result/record locals preserve intended type contracts. It does not run lower_hir_block/check_async_function and therefore cannot qualify those whole callers. All95 whole canonical compiler sites and broader gates remain unqualified. Same feature maximum3 cycles, plannedcycle2 not launched.
