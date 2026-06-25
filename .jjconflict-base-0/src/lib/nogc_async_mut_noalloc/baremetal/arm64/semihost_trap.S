.macro AC
hlt #0xF000
.endm
.macro AR
ret
.endm
.macro AW
mov x1,x0
mov x0,#0x04
.endm
.macro AE
mov x1,x0
mov x0,#0x18
.endm
.include "src/lib/nogc_async_mut_noalloc/baremetal/common/arm_semihost_trap.S"
AST simpleos_arm64_semihost_call, simpleos_arm64_semihost_write0, simpleos_arm64_semihost_exit
