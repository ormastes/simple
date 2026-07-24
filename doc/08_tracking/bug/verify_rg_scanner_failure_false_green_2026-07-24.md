# Verify treated scanner failures as clean results

Status: SOURCE-FIXED; fresh pure-Simple qualification remains pending.

## Bug

The visible-debt and quality-candidate gates returned clean results whenever
`rg` exited nonzero with empty stdout. Only exit 1 means no matches; missing
executables, I/O errors, and scanner failures use other exit codes. Those
infrastructure failures could therefore produce `STATUS: PASS`.

## Root fix

Both scan consumers use one classifier: exit 0 means matches, exit 1 means no
matches, and every other or negative exit is a release-blocking failure. The
focused contract covers normal, no-match, scanner-error, missing-command, and
spawn-failure statuses.

## Remaining qualification

Run the focused contract and one injected scanner-failure verify report through
the next fresh pure-Simple Stage 4 CLI. Seed evidence is not production
qualification.
