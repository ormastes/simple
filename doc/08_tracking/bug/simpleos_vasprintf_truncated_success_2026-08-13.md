# SimpleOS `vasprintf` truncated-success defect

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
