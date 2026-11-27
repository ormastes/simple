# Scheduler cannot qualify an existing admitted Phase2 resume

The documented scheduler `--resume-stage3-from-admitted` route reuses an
immutable Phase2. Its qualifier nevertheless waited for a new Stage2 cleanup
marker and an admission newer than the generation lease. The resume engine
produces neither. On Windows, the supervisor also replaced the receipt's
canonical `simple.exe` path with extensionless `simple`.

The scheduler now verifies the existing admission with the canonical verifier
before starting the resume, and writes a read-only lease-bound resume input
record containing the original admission and candidate identities. The
qualifier receives its measured digest and re-verifies the actual authority;
only this explicit route bypasses fresh-build cleanup/publication waiting.
The supervisor rechecks both the original record digest and full authority
before emitting lineage. Fresh builds retain the existing newer-than-lease
rule. No admission timestamp or cleanup event is manufactured.

The Stage4 continuation now computes its required planner/candidate/source/
backend binding after verification. A supplied conflicting binding refuses
continuation. The existing guard, scheduler and resume receiver share the
same calculation; the receiver still independently checks its inputs.

Focused shell fixtures use the real admission writer/verifier with explicitly
synthetic bytes; they do not execute or qualify a compiler. They cover old
admission acceptance only in resume mode, immutable identity mutations,
Windows filename preservation, record overwrite refusal, fresh-lease rules,
and the actual Stage4 hook's missing/matching/conflicting binding behavior.
The bootstrap contract CI owns bounded execution and retained owner receipts.

The first two focused CI attempts stopped in fixture setup, not production
assertions: the initial fixture omitted the Stage4 helper-path declaration;
the next checkout omitted the canonical release/version.sdn dependency and
returned exit1 without an assertion transcript. The final fixture uses a
shared constructor API with the old default layout preserved, explicitly
checks version-source prerequisites and emits numbered assertion progress.
CI includes the actual release version authority. Neither setup failure is
claimed as a compiler or admission verdict.

Deployment boundary: the scheduler derives its root, engine, qualifier and
source authority from its own checkout. It has no supported external frozen
engine override. This repair applies to matching-source generations; it must
not be copied into the active frozen f6f7 tree, and does not rewire that live
owner or claim its future Phase3/Phase4 success. The original local planner
path-conversion failure and the separate early full-CLI/runner resource
admission failures remain distinct evidence.
