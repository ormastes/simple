#include <assert.h>
#include <stdint.h>
#include "../../../../../examples/09_embedded/simple_os/arch/arm32/boot/arm32_user_transition_contract.h"

int main(void)
{
    assert(arm32_token_siphash24_kat_v13());
    return 0;
}
