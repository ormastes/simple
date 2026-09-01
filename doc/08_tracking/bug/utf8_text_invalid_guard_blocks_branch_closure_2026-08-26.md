# UTF-8 invalid-`text` guard blocks safe branch closure

## Status

Open invariant migration blocker.

## Evidence

The UTF-8 reference suite passes 58/58 and measures 97% branch coverage
(41/42). The remaining decision is the invalid-input return in
`text_without_last_codepoint`. Safe `text` values are valid UTF-8, so no safe
test can take that branch.

Removing the validation today is premature because public unchecked
byte-to-text construction still exists elsewhere in the repository. Creating
malformed `text` merely to satisfy coverage would violate the architecture.

## Required resolution

Close or proof-gate every unchecked bytes-to-`text` constructor, establish the
validated-UTF-8 invariant across native/interpreter/FFI ingress, then remove
the redundant validation branch. Re-run the owner once in a fresh verification
session and require 100% branch coverage.
