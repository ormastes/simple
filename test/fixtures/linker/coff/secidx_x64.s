// SECTION relocation against an ABSOLUTE symbol. lld writes
// numOutputSections + 1 here ("required for compatibility with MSVC",
// COFF/Chunks.cpp applySecIdx), it does NOT refuse the link.
	.data
	.globl qi
qi:
	.secidx absval
