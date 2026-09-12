# SimpleOS calendar conversion safety
**Status:** OPEN (unverified 2026-09-12)

## Status

Fixed with focused SimpleOS-header C sanitizer evidence.

## Fault

`strftime` formatted caller-owned `struct tm` years through an eight-byte
temporary buffer, allowing stack overflow for a large year. `mktime` indexed
the month table with unchecked values, and calendar/reentrant conversion APIs
could dereference null inputs.

## Repair

Calendar conversion is bounded to the documented 1970–9999 subset. `mktime`
normalizes month/day/time fields within that range; `strftime` accepts only a
canonical valid calendar record, uses a 32-byte decimal buffer, and validates
its pointers. `gmtime`, `localtime`, and reentrant wrappers reject null and
out-of-range input. The focused C harness passed with AddressSanitizer and
UBSan under the SimpleOS header ABI.

## Triage 2026-09-12
Rule D: record postdates 2026-07-29 and carries no short (<=3 min) repro; left open with a status line added since none existed. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
