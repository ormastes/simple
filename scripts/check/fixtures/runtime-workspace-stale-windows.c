/* Focused registry/Windows handle regression; no disk provisioning required. */
#include <assert.h>
#include "../../../src/runtime/runtime_workspace_storage_v1.c"
/* These text ABI hooks are not reached by the handle-only operations below. */
int64_t rt_string_len(int64_t value) { (void)value; abort(); }
const uint8_t* rt_string_data(int64_t value) { (void)value; abort(); }
int64_t rt_string_new(const uint8_t* value, uint64_t length) { (void)value; (void)length; abort(); }
int main(void) {
    assert(WS_STALE_ERROR_V1 == EBADF);
    assert(ws_origin_guard_v1() == 0);
    assert(rt_workspace_storage_release_if_absent_v1(99) == -EBADF);
    assert(rt_workspace_storage_forget_released_v1(99) == -EBADF);
    WsSlotV1* first=&ws_slots_v1[0];
    WsSlotV1* second=&ws_slots_v1[1];
    first->token=1; first->role=1;
    second->token=2; second->role=1;
    atomic_store(&first->busy,1); atomic_store(&second->busy,1);
    assert(ws_release_busy_pair_v1(first,3,second,2) == EBADF);
    assert(atomic_load(&first->busy) == 1 && atomic_load(&second->busy) == 1);
    assert(ws_release_busy_pair_v1(first,1,second,2) == 0);
    assert(atomic_load(&first->busy) == 0 && atomic_load(&second->busy) == 0);
    assert(rt_workspace_storage_forget_released_v1(1) == -EBUSY);
    assert(first->token == 1);
    first->released=1;
    assert(rt_workspace_storage_forget_released_v1(1) == 0);
    assert(first->token == 0);
    assert(rt_workspace_storage_forget_released_v1(1) == -EBADF);
    WsNativeV1 native={0}; int64_t used=17,inodes=19;
    assert(ws_native_observe_v1(&native,"leaf","pool","workspace",4096,&used,&inodes) == EBADF);
    assert(used == 17 && inodes == 19);
    return 0;
}
