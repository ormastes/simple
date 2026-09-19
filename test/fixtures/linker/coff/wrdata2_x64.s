// A second object whose `.rdata` carries MEM_WRITE, with no symbol in common
// with secrel_x64.obj: linking the two proves the flag-clash Err, not a
// duplicate-symbol Err.
	.section .rdata,"dw"
	.globl wr_cell
wr_cell:
	.long 0
