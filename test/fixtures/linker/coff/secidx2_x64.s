// Same, but an ADDR64 forces a .reloc section into existence — which lld
// COUNTS: 3 output sections here, so the SECTION value is 4, not 3.
	.data
	.globl qi
qi:
	.secidx absval
	.globl qp
qp:
	.quad qi
