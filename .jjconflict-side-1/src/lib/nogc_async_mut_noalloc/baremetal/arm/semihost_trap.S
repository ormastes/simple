.syntax unified
.thumb
.macro AC
bkpt 0xAB
.endm
.macro AR
bx lr
.endm
.macro AW
mov r1,r0
movs r0,#0x04
.endm
.macro AE
mov r1,r0
movs r0,#0x18
.endm
.include "src/lib/nogc_async_mut_noalloc/baremetal/common/arm_semihost_trap.S"
AST simpleos_arm_semihost_call, simpleos_arm_semihost_write0, simpleos_arm_semihost_exit
