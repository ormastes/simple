// FreeBSD crt1.o/crti.o shape: both carry the ABI tag in COMDAT group
// .freebsd.noteG; ld.lld keeps only the first copy.
    .section .note.tag,"aG",%note,.freebsd.noteG,comdat
    .p2align 2
    .long 8, 4, 1
    .asciz "FreeBSD"
    .long 1404000
