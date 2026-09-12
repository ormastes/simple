# Pure-Simple Default-Trait `is_empty` Link Gap
**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

## Status

Open compiler-owner defect with bounded source compatibility applied to the
three Stage-4 modules that blocked the SimpleOS memory-leveling build.

## Failure

The pure-Simple native pipeline can resolve built-in array or text
`is_empty()` calls to the default `Len.is_empty` or
`ExactSizeIterator.is_empty` trait symbol without emitting that default body.
Stage-4 then fails with an undefined reference.

## Compatibility

Affected built-in checks in the Lean backend, Lean MIR translator, and easy-fix
lint rules use the equivalent direct expression `len() == 0` (or `!= 0`). This
keeps native lowering on the existing tag-aware length path and does not alter
user-defined `is_empty` methods.

## Required Owner Fix

Native trait lowering must materialize reachable default method bodies or
rewrite a default call through the concrete receiver implementation. Once that
is verified for arrays, strings, Dicts, and custom trait implementors, these
compatibility expressions may return to the standard API spelling.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no short (<=3 min) repro; closed stale per the standing triage decision. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
