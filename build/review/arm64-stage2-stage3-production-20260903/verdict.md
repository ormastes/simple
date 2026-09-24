# arm64 Stage2→Stage3 production attempt

- Source commit: `777cf9ad5a3`
- Admitted parent: `/Users/ormastes/simple/bin/release/macos-arm64/simple`
- Parent SHA-256: `277f8ac9e14ae266ce380a5890d434ce27b47cee9378e2b337cbcc8cd4086767`
- Command phase attempted: producer-authorized `--stop-after-stage2`
- Invocation count: exactly one
- Exit status: `1`
- Verdict: blocked before Stage2 compilation
- Available filesystem space at diagnosis: `6,626,444 KiB`
- Required bootstrap floor: `10 GiB`

The bootstrap correctly refused to start because the filesystem was below its
documented safety floor. No Stage2 artifact, planner admission, Stage3 command,
or producer receipt was created. The disk guard was not weakened, no binary was
copied into Stage2, no receipt was synthesized, and no Rust seed was used.

`stage2-producer.stdout.log`, `stage2-producer.stderr.log`,
`stage2-producer.exit-status`, and `environment.env` are the exact retained
evidence from the invocation.
