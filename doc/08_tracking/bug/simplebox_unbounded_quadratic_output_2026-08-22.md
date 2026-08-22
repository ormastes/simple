# SimpleBox unbounded/quadratic output (fixed in source)

## Failure

`echo` accumulated its response with `output = output + piece`. For `n` bytes
split across arguments this copied a growing prefix and therefore required
O(n²) byte-copy work. `seq` accepted an arbitrary parsed count and printed until
that count, so one guest command could monopolize CPU and produce unbounded
output.

## Fix contract

- `echo` retains argument/separator parts in one linear pass and joins once.
- `echo` and `seq` admit at most 65,536 output bytes, including newlines.
- Oversized requests fail before any requested output is written; accepted
  inputs retain their existing byte output and exit status.
- `seq` preflight is bounded by the output cap even when its parsed count is
  extremely large.
- Seq admission uses a checked decimal scanner rather than trusting the libc
  parser's unchecked accumulator. It rejects counts above 12,773 and numeric
  arguments above 64 bytes, including inputs that would wrap to a negative or
  small positive `i64`.

Focused specs cover exact output, `-n`, the byte boundary, rejection, retained
piece count, seq byte accounting, checked wrap strings, negative/suffix
compatibility, and bounded preflight work.

## Remaining execution evidence

The worktree has no admitted self-hosted `bin/simple`, so runtime timing, peak
RSS, and the Simple optimizer cannot be run honestly in this lane. This is an
environment/bootstrap evidence blocker, not permission to use the Rust seed.
