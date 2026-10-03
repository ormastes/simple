.option norelax
.option rvc
.section .text.worker,"ax",@progbits
.globl worker
worker:
  li a0, 42
  ret
.section .text.done,"ax",@progbits
.globl done_label
done_label:
  li a7, 93
  ecall
.section .text.fail,"ax",@progbits
.globl fail_label
fail_label:
  li a0, 99
  li a7, 93
  ecall
.data
.globl data_value
.type data_value,@object
data_value:
  .word 41
.size data_value, 4
