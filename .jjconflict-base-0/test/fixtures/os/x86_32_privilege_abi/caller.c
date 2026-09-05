#include "../../../../src/os/kernel/arch/x86_32/privilege_abi_v1_8.h"

void _start(void)
{
    SimpleOsX86_32TrapFrameV1 frame = {0};
    SimpleOsX86_32PrivilegeTokenV1 token = {0};
    SimpleOsX86_32TrapDispositionV1 out = {0};
    token.expected_cr3 = 0x1000U;
    (void)simpleos_x86_32_privilege_dispatch_v1_1(&frame, &token, 0x1000U, &out);
    for (;;) __asm__ volatile("hlt");
}
