/* NEW negative classification prevention witness. Includes the real owner and
 * its exact rollback-retention constructor. Invalid fixture descriptors ensure
 * this cannot manufacture successful cgroup cleanup or ordinary reaped proof.
 * Link normal CoreC providers; no support-symbol fakes. */
#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE
#endif
#include "../runtime_process_owned.c"
#include <assert.h>
#if !defined(__linux__) || defined(RT_PROCESS_OWNED_CORE_ONLY)
int main(void){return 77;}
#else
static void denied_observation(SplArray* receipt,int expected_error) {
    assert(receipt&&rt_array_len(receipt)==10);
    assert(rt_value_as_int(rt_array_get(receipt,0))==expected_error);
    assert(rt_value_as_int(rt_array_get(receipt,1))==0); /* never terminal child */
    assert(rt_value_as_int(rt_array_get(receipt,2))==0); /* no reaped leader */
    rt_array_free(receipt);
}
int main(void) {
    const char* root="/not-accessed-by-classification";
    const char* identity="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    const char* other="bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
    rt_lg_retain_unlaunched_scope_v2(-1,-1,"test-no-child",root,identity,0);
    assert(rt_linux_group.active&&rt_linux_group.no_child_scope);
    assert(rt_linux_group.pid==0&&!rt_linux_group.leader_reaped&&!rt_linux_group.collected);
    assert(rt_linux_group_stream_no_child_scope_v2(root,strlen(root),identity,64)==1);
    assert(rt_linux_group_stream_no_child_scope_v2(root,strlen(root),other,64)==-2);
    assert(rt_lg_poll(&rt_linux_group)==EPROTO); /* rejects before any wait or FD probe */
    denied_observation(rt_linux_group_poll_v1(1),EPROTO);
    denied_observation(rt_linux_group_collect_v1(1),EPROTO);
    denied_observation(rt_linux_group_collected_stream_v2(1),EINVAL);
    assert(rt_linux_group_stream_collect_no_child_v2(root,strlen(root),other,64)==ESTALE);
    assert(rt_linux_group_stream_collect_no_child_v2(root,strlen(root),identity,64)!=0);
    assert(rt_linux_group.active&&!rt_linux_group.collected&&!rt_linux_group.leader_reaped);
    assert(rt_linux_group.no_child_scope&&rt_linux_group.pid==0);
    /* Fixture owns no real FDs or cgroup; reset only its test state. No positive
     * terminal/unlaunched cleanup proof is published or asserted. */
    memset(&rt_linux_group,0,sizeof(rt_linux_group));
    puts("PASS negative classification: no-child scope cannot emit reaped-tree evidence");
    return 0;
}
#endif
