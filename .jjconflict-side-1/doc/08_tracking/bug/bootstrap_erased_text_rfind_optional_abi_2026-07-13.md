# Bootstrap erased-text `rfind` loses Optional not-found semantics

## Status

Open. Tracked by TODO 559.

## Problem

The pure-Simple Stage4 bootstrap MIR fallback for an unresolved erased-text
receiver now selects the canonical `rt_string_rfind` runtime owner. That ABI
returns `-1` when the needle is absent, while the language API is `i64?` and
normally exposes `nil` for absence. The current full-CLI closure only coalesces
the result before comparing it, so restoring the owner fixes linking without
changing that caller, but the fallback is not a general semantic solution.

## Required fix

Preserve the receiver and method-result type through HIR/MIR so normal text
method lowering owns `replace(...).rfind(...)`, or adapt the runtime result into
the canonical Optional representation. Add executable found and missing-needle
coverage before removing TODO 559. Do not add a second runtime string-search
owner or a caller-specific constant.
