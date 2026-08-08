# spipe-docgen mixed help bypassed validation

Status: SOURCE-FIXED; fresh pure-Simple qualification remains pending.

## Bug

Any invocation containing `--help` or `-h` returned success before parsing the
remaining arguments. Missing inputs and misspelled options could therefore
false-green without generating documentation.

## Root fix

After normalizing the optional direct-owner command token, help succeeds only
when it is the sole argument. Mixed or repeated help returns exit 2 before
creating an output directory. The focused docgen contract
covers sole help, mixed help, unknown mixed help, and no filesystem mutation.

## Remaining qualification

Run the focused scenario once through the next fresh pure-Simple Stage 4 CLI.
Seed or stale-runner evidence remains source evidence only.
