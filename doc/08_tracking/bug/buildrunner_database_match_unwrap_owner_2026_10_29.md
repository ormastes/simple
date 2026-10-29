# BuildRunner database owner lost after match and optional unwrap

Status: app compatibility fix verified through native MIR; compiler inference and full manager qualification OPEN.

The source-matched manager build with recovered P2
`0d6f2e4720845195c9f91de292056fac4c57cabef81390507c78d95e51133a28`
reached MIR after 307 HIR cache hits, but could not resolve `settle`, `is_err`,
`finish` and `unwrap_err` at `phase_admission.spl:985-990`. The receiver follows
an imported `Result<BuildRunnerDatabaseSessionV1?, text>` producer, a value-match
that returns on Err, a nil refusal and `val database = maybe_database!`.

The method bodies are required ownership gates: settlement records terminal
rows and finish publishes the journal revision. Removing or bypassing them is
not a repair. MIR aggregation refused linkage and no manager artifact was
published; the placeholder warning is not evidence of a successful executable.

Evidence: `/private/tmp/lunar-buildrunner-manager-20261029/build-10g-600s.log`.
The cross-module native probe `test/fixtures/buildrunner/session_unwrap_repro.spl`
uses the same return/match/unwrap shape. Its settle method mutates state and
finish returns 42 only after that mutation; native stdout and exit must prove
both method calls execute.

The earlier manager attempts reached a wall deadline and then the 8 GiB
resource limit. The 10 GiB attempt retained resource enforcement and exposed
this semantic failure. These are distinct terminal outcomes, not passes.

## Native probe evidence

The unannotated imported-class probe failed MIR at the chained `is_err` call
(receiver has no HIR type), exit 1, no artifact. The otherwise identical
`session_unwrap_typed.spl` names `SessionProbe` at the local binding: build
exit 0, actual native stdout `42` plus LF, exit 0. Since finish returns an
error unless settle changed its state to 41, this proves both methods executed.
The minimal failure is narrower than the manager's five unresolved calls; do
not claim that every inference shape is fixed.

- Red log: `/private/tmp/lunar-buildrunner-manager-20261029/session-probe-red-ready.log`,
  SHA-256 `de96e6a7c603b3053e02529a73faa1d29706ecb3a63d71ffbae4faad2eb585ad`.
- Green log: `session-probe-typed-green.log` in the same directory, SHA-256
  `29bafd856bb6311fac95ceb72cc5d120826b60fa2bccb6d9978bbad09eba9c93`.
- Native artifact: `session-probe-typed-green`, SHA-256
  `21f0d35c1e0ca94b1aa0ad58262b4b93e259dc4e04fd3fa52cfbb70e5679a73c`.
- Execution log: `session-probe-typed-green.run.log`, SHA-256
  `084c799cd551dd1d8d5c5f9a5d593b2e931f5e36122ee5c793c1d08a19839cc0`.

These are focused native diagnostic probes, not a qualified manager/provider.
The retained link command records generated C runtime objects. The current
compiler source describes unresolved calls as fatal; the recovered producer
uses an older placeholder warning. Both observed manager and probe failures
blocked linkage, so no silent-success executable was observed.

The app correction preserves the explicit `BuildRunnerDatabaseSessionV1`
receiver and keeps every nil, settle, finish and error check. The underlying
compiler inference issue stays OPEN; removal of the compatibility annotation
requires a rebuilt producer to pass the unannotated native probe and manager.

## Canonical tracking maintenance limitation

The deployed pure-Simple `bug-add` command exited 1 with `--fork requires
hosted interpreter support` (`/private/tmp/astra-buildrunner-bug-add.log`).
The same canonical `src/app/bug_add/main.spl` through the explicitly authorized
hosted maintenance runner exited 1: `failed to create bug database without
replacing an existing path` (`/private/tmp/astra-buildrunner-bug-add-hosted.log`).
The database was preserved byte-for-byte; no CRC editing or replacement was
attempted. `bin/bug` points to an absent tool.

Following `.claude/skills/lib/debug_ladder.md`'s documented unavailable-tool
fallback, this hand-written record remains authoritative for the lane. The
source uses an ordinary compatibility comment referencing it, not an unknown
`@workaround` machine tag that would break index refresh. Canonical registration
owner: bug tooling; unblock by restoring a writer that can read the existing
database and add this exact ID without replacing it. An earlier annotated
build captured the old machine-tag warning; that is not the final comment.

## Corrected manager and scenario result

With the annotation and the reviewed original entry/runtime/cache route, the
manager passed MIR 307/307 and AOP 307/307, clearing all five original receiver
errors. Native code generation then failed at the separate Cranelift exported
module-static accessor boundary in `lib.scv.alloc_bounds`; no manager image
was published. Log: `buildrunner-annotated-corrected.log` in the directory above,
SHA-256 `6deb3b36e9166389b8a97928e13252b9a47dfbfe52fa0f6a37583271d795131e`.
An intervening attempt with drifted runtime/cache/entry arguments was cancelled
(exit 143), retained as setup failure, and not used as annotation evidence.

`test/01_unit/app/buildrunner/database_session_owner_spec.spl` additionally
executed the finish-before-settle error and finish-after-settle success under
the explicitly opted-in hosted diagnostic runner: one scenario passed, exit 0.
Log: `/private/tmp/lunar-buildrunner-database-session-owner-seed.log`, SHA-256
`934ce4bba439c02106ec79e6ee269953d88d66fcc163286e399183bbcf10fc85`.
That SSpec result is diagnostic only; native error-branch execution and a
qualified SSpec runner remain unverified.
