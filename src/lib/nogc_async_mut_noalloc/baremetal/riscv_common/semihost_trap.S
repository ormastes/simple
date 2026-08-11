.section .text
.align 2
.macro RST c,w,e
.global \c
\c:
.option push
.option norvc
slli zero,zero,0x1f
ebreak
srai zero,zero,0x7
.option pop
ret
.global \w
\w:
mv a1,a0
li a0,0x04
tail \c
.global \e
\e:
mv a1,a0
li a0,0x18
tail \c
.endm
