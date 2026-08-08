.section .text
.align 2
.macro AST c,w,e
.global \c
\c:
AC
AR
.global \w
\w:
AW
b \c
.global \e
\e:
AE
b \c
.endm
