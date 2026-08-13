# Project statistics self-hosted generation blocked

## Status

Partially resolved — parser repaired; current admitted CLI/PPTX generation remains blocked.

## Evidence

- The shared `VerificationIrModuleV1.closure_ready` condition was corrected to
  parenthesize its multi-line boolean expression; the feature system spec now passes.
- Focused Markdown renderer and SimpleOS PPTX theme specs also pass.
- `bin/simple stats --quality=summary` refuses execution because the installed
  binary identifies itself as the Rust bootstrap seed and the pure-Simple
  `stats` tool is unavailable.
- `bin/simple spipe-docgen ... --no-index` succeeds with 1/1 complete manuals
  and 0 stubs, so documentation generation itself is not the blocker.

## Impact

Markdown, TLDR, and SimpleOS-native slide source are generated. A current
native PPTX cannot yet be produced because no admitted current full CLI exists.

## Unblock condition

Complete the preserved-cache strict full-CLI build and deploy an admitted
pure-Simple `bin/simple`. Then run `bin/simple stats --quality=summary`, confirm
the generated PPTX, and repeat the release verification gate.
