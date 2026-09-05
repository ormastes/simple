#include "../../../../src/os/kernel/arch/x86_32/privilege_abi_v1_8.h"

simpleos_x32_i32 simpleos_x86_32_privilege_dispatch_v1_1(
    const SimpleOsX86_32TrapFrameV1 *frame,
    SimpleOsX86_32PrivilegeTokenV1 *token,
    simpleos_x32_u32 observed_cr3,
    SimpleOsX86_32TrapDispositionV1 *out)
{
    if (!frame || !token || !out) return -22;
    if ((((simpleos_x32_u32)frame | (simpleos_x32_u32)token |
          (simpleos_x32_u32)out) & 3U) != 0U) return -22;
    if (observed_cr3 != token->expected_cr3) return -13;
    out->action = 0;
    out->eax = -38;
    out->kernel_esp = 0;
    out->kernel_eip = 0;
    return 0;
}
