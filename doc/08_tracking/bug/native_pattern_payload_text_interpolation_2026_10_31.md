# Native: text payload bound by enum pattern prints as integer

**Status:** Open (not tested on a rebuilt compiler)
**Severity:** P2
**Date:** 2026-10-31

## Symptom

On the pinned producer, a text payload bound by an enum pattern, `MalformedSchema(message)`, printed as a raw 13-digit integer through both `"{message}"` and `"x: " + message`. Calling `.len()` and `.contains()` on the same binding worked.

## Evidence

- Seen in `fresh_secured_db` and `sqlcipher4_error_text`.

## Unverified

- Whether the defect reproduces on a rebuilt compiler. Not tested.
- Whether the cause is in pattern binding or in text interpolation and concatenation.
