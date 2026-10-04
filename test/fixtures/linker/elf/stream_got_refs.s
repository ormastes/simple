.text
.globl _start
_start:
  .ascii "GOTCASE!"
  mov got_value@GOTPCREL_NORELAX(%rip), %rax
  call *got_function@GOTPCREL(%rip)
  mov got_value@GOTPCREL(%rip), %rax
  ret
