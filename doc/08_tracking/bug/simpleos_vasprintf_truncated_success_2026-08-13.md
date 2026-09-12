# SimpleOS `vasprintf` truncated-success defect
**Status:** OPEN (unverified 2026-09-12)

## Status

Fixed with focused host-C evidence; target-native sysroot execution remains pending.

## Fault

The former implementation formatted into a fixed 4 KiB allocation and returned
the full `vsnprintf` length. For text above that size it therefore published a
truncated string while reporting an exact successful length.

## Repair

`simpleos_libc_ext.c` now measures with a copied `va_list`, performs checked
`length + 1` allocation, renders with a second copied list, and frees/fails
closed if the second pass disagrees. The focused C harness exercises a 5,014
byte result and null output-pointer rejection.

## Triage 2026-09-12
Rule D: record postdates 2026-07-29 and carries no short (<=3 min) repro; left open with a status line added since none existed. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
