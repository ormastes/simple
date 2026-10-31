# Pinned stage2 native string interpolation fails right after an escaped quote (2026-10-31)

Status: OPEN. Found by the devhub-phase12 goal lane during phase-1 native artifact
qualification (pinned phase-1 compiler sha 6c5c53aa).

Symptom: in a native build, `print "a \"{V} b\""` (interpolation opening immediately
after an escaped quote `\"`) prints the literal `{V}`; the same source under the
Rust seed (interpreter or native) interpolates correctly. Interpolation elsewhere in
the string (e.g. `a \"x\" {V} b`) works under both. Minimal repro built with the
pinned compiler at build/devhub-goal/probe-interp2 (kept for replay).

Impact: any devhub (or other) native print of JSON-ish strings with escaped quotes
around an interpolation site silently emits literal `{NAME}` text. Repro surfaced
via test/03_system/app/devhub/feature/devhub_cli_process_spec.spl ("machine readable
version output").

Workaround: concatenate the interpolated value (`"...\"" + V + "\"..."`), tagged
`@workaround bug=pinned-stage2-native-string-interp-20261031`.

Removal condition: retire when a stage2 containing the fix bootstraps (likely a
string-lexer/MIR-string-construction fix in 10.frontend/50.mir).
