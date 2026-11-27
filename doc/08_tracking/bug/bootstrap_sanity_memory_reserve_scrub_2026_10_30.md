# Stage2 sanity drops the configured build memory reserve

Status: fixed in source; focused shell-execution regression passes; canonical admission not rerun.

Linux P2 linked with compiled=2 reused=1614 failed=0, but canonical frontend
sanity refused before SCV inventory generation: available11262MiB was below the
default24576MiB reserve. The supported SIMPLE_BUILD_MEMORY_RESERVE_BYTES caller
setting is removed by bootstrap_stage_sanity's environment scrub.
Rejected candidate SHA256: ca2e62284198137f01cb99f32b6dcd530647ce587ed29bfc102ba5477f5411b3.
Retain failed admission; no P2 qualification follows merely from linking.

Scope: validate and preserve only an explicitly configured positive canonical
i64 byte reserve. Absence keeps the compiler default. No broader environment
allowlist, hard-cap change, runtime semantic change or frozen Linux edit.

The canonical wrapper now records presence and validates an explicit reserve
before any candidate call: decimal digits, no leading zero, positive and at
most9223372036854775807. It restores and exports the exact value after the real
scrub. Absence stays absent, retaining the compiler-owned24GiB default. Other
SIMPLE variables remain scrubbed. The existing byte-to-KiB interpretation is
unchanged; this control is a headroom threshold, not a memory hard cap.

Validation executed the actual sanity-function prefix and scrub in /bin/sh,
then a separate real child reports its environment. No compiler was executed.
Three tests cover14 cases: absent, three valid values including1GiB and i64max,
and10 invalid values including empty/zero/sign/leadingzero/whitespace/overflow.
Before fix:13 failing subcases; after fix:3 tests pass. The unrelated environment
sentinel remains absent in successful cases; invalid cases refuse125 before the
child witness. POSIX fixture is explicitly skipped on non-POSIX hosts.

Red log: /private/tmp/astra-sanity-reserve-red.log
SHA25654330f69040440f5153afc0a86d5687926d2bc26a236b35a291d979a90de3eff.
Green log: /private/tmp/astra-sanity-reserve-green.log
SHA25695425af7acf26b46234db23c79372841b5831841df741433c8226ac8a4835872.

Broader sanity-base-controls suite has an existing archived writer pin mismatch:
baseline425041d7 runs9 tests:5pass,1error,3skip; changed suite runs12 tests:
8pass,1sameerror,3skip. `test_actual_writer_mutation` reports `changed actual
fresh writer` in untouched sanity-control-functions.shs. No historical pin or
receipt was relaxed. Retained logs: /private/tmp/astra-sanity-controls-baseline.log
and /private/tmp/astra-sanity-controls-full.log.

Live diagnostic policy is a separately recorded1GiB positive reserve with the
same9.5GiB enforced supervisor cap and10GiB container, one worker. That direct
Hello attempt does not retroactively accept the rejected canonical admission.
The frozen af664 Linux source was not edited by this patch.
