# Must-Check Tiering Feature Expert

Keep interactive push validation near ten seconds. Do not add compiler builds,
full tests, QEMU/hardware work, or benchmark campaigns to the push driver. Add
expensive requirements to `config/check/must_check_gates.sdn` and produce their
evidence through `check-bootstrap-must-pass.shs`.

Compiler Stage 1-4 rows are push-blocking and may be promoted only after the
Stage 2/3 full-provenance verifier and exact Stage 4 post-bootstrap acceptance
oracle pass. Bootstrap completion then runs every automated registry row and
records its retained log; do not require a second operator command. PASS needs
a UTC timestamp and evidence reference. TODO and blocked rows remain visible
and never count as PASS.
