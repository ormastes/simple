# Push rules gate reads the working registry for a committed ref

Status: RESOLVED — `codex/session-01a023a8`

## Failure

`check-rules-sdl.shs --ref <commit>` correctly supplies `<commit>` to each rule
command, but parses rule IDs, groups, commands, and floors from the current
working-tree `rules.sdl`. A concurrent or dirty local edit can therefore change
what an otherwise committed push check executes, including injecting an
unbounded `sh -c` command. This contradicts the script's committed-content
contract and the closed push-policy model.

## Required fix

Unless an explicit `--rules` diagnostic fixture is supplied, load `rules.sdl`
from the exact verified `--ref` into an isolated temporary file before parsing.
Add a regression proving a hostile working-tree rule does not affect a ref scan.

## Resolution

Normal scans now extract `rules.sdl` from the verified commit into an isolated
temporary file; only explicit diagnostic `--rules` fixtures bypass that route.
The must-check source fingerprint now includes `rules.sdl` in both bootstrap
production and push consumption.

The focused fixture commits a passing registry, replaces the working copy with
a hostile `sleep 30; echo 0` rule, and proves the committed scan still passes.
The complete focused contract passed in 7.61 seconds with 71,936 KiB peak RSS;
the committed-ref and installed-hook paths reported 0s and 1s.
