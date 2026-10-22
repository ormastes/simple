# Failed artifact action terminalization

REQ-IM-007. Executable: `test/03_system/compiler/incremental/artifact_failure_terminalization_spec.spl`.
Status: authored; runtime and docgen UNRUN.

1. Claim an action, then return failure or cancellation with no output identity.
   The actual bridge must accept the terminal result, set both owners to the
   corresponding terminal state, release reserved memory and publish no CAS
   artifact. Ordinary failure retains nonempty `action-failed`; cancellation
   retains `cancelled`.
2. Deliver the terminal result again. It must fail without a second release.
   The original immutable input route must still retain its running reservation.
3. Repeat failure/cancellation with the same owner/token but an older dispatch
   generation. Both must fail before releasing the current reservation.
4. Submit success with an empty output identity. It must remain rejected.

The previous bridge rejected all empty output identities before inspecting
success. Failed groups therefore could not reach their terminal state. The
repair limits that guard to successful publication. Existing coordinator and
artifact protocol validation still run; no synthetic success or artifact is
introduced. These are sequential production API regressions, not live process
or complete grouped runner qualification.
