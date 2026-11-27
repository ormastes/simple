/* Link-only ABI fixture. Compile twice with a RISC-V/ARM-enabled clang:
 * --target=armv7a-none-eabi -mfpu=vfpv3-d16 -mfloat-abi=soft
 *   -DARM_ABI_FN=arm_soft_entry -ffreestanding -c arm_float_abi.c -o arm_abi_soft.o
 * --target=armv7a-none-eabi -mfpu=vfpv3-d16 -mfloat-abi=hard
 *   -DARM_ABI_FN=arm_hard_entry -ffreestanding -c arm_float_abi.c -o arm_abi_hard.o
 * Both ET_REL files carry e_flags=0x05000000. Hard-float convention is
 * recorded by Tag_ABI_VFP_args=1; the soft C ABI uses the default base AAPCS.
 */
float ARM_ABI_FN(float value) { return value; }
