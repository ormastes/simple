// SECREL / SECTION / ADDR32NB fixture. clang's COFF assembler is the only
// way to emit these three from this toolchain (C never produces them here).
	.text
	.globl	anchor
anchor:
	retq
	.section .rdata,"dr"
	.globl	reloc_tbl
reloc_tbl:
	.secrel32 anchor        // IMAGE_REL_AMD64_SECREL
	.secidx   anchor        // IMAGE_REL_AMD64_SECTION
	.short    0             // pad to 4-byte boundary
	.long     anchor@IMGREL // IMAGE_REL_AMD64_ADDR32NB
