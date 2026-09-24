# Portable body parameter-header budget

This focused regression proves that portable HIR validation reserves the
function parameter headers that bound signature matching before it compares
the corresponding parameter-type arrays.

## Scenario: oversized headers refuse before matching

Given a private function whose body declares one `i64` parameter, whose symbol
signature instead declares one `bool` parameter, and whose shared ledger allows
zero parameters, semantic validation must return a typed `BoundsExceeded`
error containing `parameter budget`.

The mismatched types make the ordering observable: an unreserved matching pass
would return an unsupported-signature result first. The required bounds error
therefore demonstrates fail-closed reservation under a tiny limit.

## Scenario: caller-first call matching is also bounded

Given an exported caller with the lowest function symbol ID and a later private
callee with one parameter, the same zero-parameter ledger must refuse before
the caller body can compare its mismatched callee-expression signature.

This separately covers the call-site matcher: all module function headers are
reserved in a preflight, rather than only when each sorted function body begins.
