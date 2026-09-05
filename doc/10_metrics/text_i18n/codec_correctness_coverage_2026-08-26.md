# Generic codec correctness and coverage — 2026-08-26

The generic codec now reconstructs Unicode text from decoded scalar values
instead of converting each UTF-8 lead/continuation byte independently. ASCII
encoding emits one `?` for each unsupported scalar.

The third and final bounded cycle passed 30/30 examples, including multilingual
UTF-8/16/32 roundtrips, malformed UTF-8 replacement, ASCII and Latin-1 range
policies, identity transcoding, every codec enum arm, registry aliases, endian
paths, and byte/control helper classes.

Coverage is 94% lines (93/98) and 45% branches (29/64). The branch denominator
includes short-circuit paths through every spelling alternative in registry
alias expressions. This evidence does not claim 100% for the owner.

Remaining production work:

- replace unknown-name fallback with a typed error;
- replace intermediate codepoint arrays with direct streaming `TextSink` output;
- measure allocation count/bytes, temporary workspace, capacity growth, and
  isolated peak RSS before and after that conversion.
