// An ADDR64 to a REAL symbol in a section marked IMAGE_SCN_MEM_DISCARDABLE.
// Bytes 99 AND 139 are patched 0xC0 -> 0xC2, setting DISCARDABLE on .data and
// on .bss (which merges into .data, so both must agree on the flag). lld skips
// DISCARDABLE sections when collecting base relocations: the golden has NO .reloc.
	.text
	.globl disc_entry
disc_entry:
	retq
	.data
	.globl dptr
dptr:
	.quad disc_entry
