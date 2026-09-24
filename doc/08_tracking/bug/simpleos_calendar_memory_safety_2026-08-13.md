# SimpleOS calendar conversion safety
## Closed 2026-09-16 — Status "Fixed"; repair + focused ASan/UBSan harness evidence

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

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

