@ Architecture-only assembly is compatible with either C float convention.
@ clang --target=armv7a-none-eabi -c arm_float_neutral.s -o arm_abi_neutral.o
.text
.arm
.globl arm_neutral
.type arm_neutral,%function
arm_neutral:
    bx lr
.size arm_neutral, .-arm_neutral
