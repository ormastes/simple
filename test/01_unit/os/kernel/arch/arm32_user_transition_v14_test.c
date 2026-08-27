#include <assert.h>
#include <stdint.h>
#include "../../../../../examples/09_embedded/simple_os/arch/arm32/boot/arm32_user_transition_contract.h"

int main(void)
{
    uint8_t secret[16]={1};
    _Alignas(8) Arm32SvcFrameV1 frame={0};
    Arm32UserHandoffTokenV1 token;
    Arm32SvcDispositionV14 d, forged;
    uint32_t top=(uint32_t)(uintptr_t)&frame+sizeof frame;
    assert(arm32_token_registry_bootstrap_v11(1,secret));
    assert(arm32_token_issue_v11(0,&token,7,3,9,0x40400000,
        UINT64_C(0x1122334455667788),top,0x40201000,0x40300000));
    assert(arm32_token_advance_v11(0,ARM32_TOKEN_PREPARED,ARM32_TOKEN_RUNNING));
    frame.spsr=ARM32_CPSR_USR; frame.return_pc=0x400000; frame.r[7]=60; frame.r[0]='A';
    assert(arm32_svc_dispatch_disposition_v14(0,&frame,0x40400000,&d));
    forged=d; forged.task_generation++;
    assert(arm32_scheduler_commit_disposition_v14(0,&forged)==ARM32_SVC_ACTION_REJECT);
    forged=d; forged.auth_receipt_lo^=1;
    assert(arm32_scheduler_commit_disposition_v14(0,&forged)==ARM32_SVC_ACTION_REJECT);
    assert(arm32_scheduler_commit_disposition_v14(0,&d)==ARM32_SVC_ACTION_RETURN_USER);
    assert(arm32_scheduler_stdout_len_v14(0)==1);
    uint8_t stdout_byte=0;
    assert(arm32_scheduler_stdout_copy_v14(0,&stdout_byte,1));
    assert(stdout_byte=='A');
    assert(arm32_scheduler_commit_disposition_v14(0,&d)==ARM32_SVC_ACTION_REJECT);
    frame.r[7]=0; frame.r[0]=37;
    assert(arm32_svc_dispatch_disposition_v14(0,&frame,0x40400000,&d));
    assert(arm32_scheduler_commit_disposition_v14(0,&d)==ARM32_SVC_ACTION_RESUME_SUPERVISOR);
    return 0;
}
