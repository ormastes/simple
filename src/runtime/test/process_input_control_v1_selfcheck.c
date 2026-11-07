/* NOT_RUN. Actual pipe/write-gate transport witness, NOT cgroup admission or
 * lifecycle evidence. Normal CoreC providers; include runtime_process.c once. */
#define _GNU_SOURCE
#include "../runtime_process.c"
#include <assert.h>
#ifndef __linux__
int main(void){return 77;}
#else
static const char* id="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
static const char* target="bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
static const char* nonce="cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc";
static int64_t word(SplArray* a,int i){assert(a);return rt_value_as_int(rt_array_get(a,i));}
static void mutation(SplArray* a,int expected){assert(a&&rt_array_len(a)==2);assert(word(a,0)==expected);if(!expected)assert(word(a,1)==1);rt_array_free(a);}
#define REF child,generation,root,strlen(root),id,64
#define META target,64,nonce,64
static void preenable_fork(pid_t child,int64_t generation,const char* root,int held){
    int gate[2];assert(pipe2(gate,O_CLOEXEC)==0);
    if(held)pthread_mutex_lock(&s_proc_lock);
    pid_t attacker=fork();assert(attacker>=0);
    if(!attacker){
        alarm(2);close(gate[1]);char go;assert(read(gate[0],&go,1)==1);
        assert(rt_process_write_stdin_some_owned_v2(REF,"BAD",3,0,3)==-10);_exit(0);
    }
    if(held)pthread_mutex_unlock(&s_proc_lock);
    close(gate[0]);mutation(rt_process_input_enable_v1(REF),0);
    assert(write(gate[1],"!",1)==1);close(gate[1]);int status;
    assert(waitpid(attacker,&status,0)==attacker&&WIFEXITED(status)&&WEXITSTATUS(status)==0);
}
int main(void){
    alarm(15);char root[]="/tmp/simple-input-barrier-XXXXXX";assert(mkdtemp(root));
    int64_t generation=rt_process_stream_reserve_v2();assert(generation>0);
    assert(rt_process_stream_bind_v2(generation,root,strlen(root),id,64)==0);
    int input,output,directory;
    assert(rt_process_stream_claim_launch_v2(generation,root,strlen(root),id,64,&input,&output,&directory)==0);
    pid_t child=fork();assert(child>=0);
    if(!child){alarm(12);assert(syscall(SYS_close_range,3U,~0U,0U)==0);for(;;)pause();}
    close(output);close(directory);
    assert(rt_process_stream_publish_broker_v2(generation,root,strlen(root),id,64,child)==0);
    /* The test owns this actual duplicated child-facing read FD, not lifecycle
     * proof. The real child owns no test receipt or invented terminal marker. */
    assert(fcntl(input,F_SETFL,fcntl(input,F_GETFL)|O_NONBLOCK)==0);
    preenable_fork(child,generation,root,0);
    /* Fresh second slot: held-gate fork also occurs BEFORE enable. */
    int64_t second=rt_process_stream_reserve_v2();assert(second>generation);
    assert(rt_process_stream_bind_v2(second,root,strlen(root),id,64)==0);
    int second_in,second_out,second_dir;
    assert(rt_process_stream_claim_launch_v2(second,root,strlen(root),id,64,&second_in,&second_out,&second_dir)==0);
    assert(rt_process_stream_publish_broker_v2(second,root,strlen(root),id,64,child)==0);
    preenable_fork(child,second,root,1);
    close(second_in);close(second_out);close(second_dir);
    pthread_mutex_lock(&s_proc_lock);struct RtProcSlot* second_slot=stream_action_locked_v2(child,second,root,strlen(root),id,64);
    assert(second_slot);proc_free_locked(second_slot);pthread_mutex_unlock(&s_proc_lock);
    assert(rt_process_write_stdin_some_owned_v2(REF,"BAD",3,0,3)==-1);
    assert(rt_process_write_stdin_some_ref_v1(child,generation,"BAD",3,0,3)==-2);
    assert(rt_process_write_stdin_some(child,"BAD",3,0,3)==-1);
    assert(!rt_process_write_stdin(child,"BAD"));
    char bytes[8192];assert(read(input,bytes,sizeof(bytes))==-1&&errno==EAGAIN);
    int64_t now;assert(input_now_v1(&now));int64_t expiry=now+5000000000LL;
    mutation(rt_process_input_install_v1(REF,META,1,expiry),0);
    mutation(rt_process_input_install_v1(REF,META,1,expiry),0);
    SplArray* a=rt_process_input_write_some_v1(REF,META,1,1,"prefix",6,1,3);
    assert(word(a,0)==0&&word(a,1)==1&&word(a,2)==1&&word(a,3)==3);rt_array_free(a);
    assert(read(input,bytes,sizeof(bytes))==3&&memcmp(bytes,"ref",3)==0);
    a=rt_process_input_write_some_v1(REF,META,1,1,"BAD",3,0,3);
    assert(word(a,0)==-15&&word(a,1)==0);rt_array_free(a);
    a=rt_process_input_state_v1(REF);assert(rt_array_len(a)==268&&word(a,5)==1&&word(a,6)==1&&word(a,7)==3);rt_array_free(a);
    /* Actual finite pipe saturation, not a fabricated zero-write result. */
    memset(bytes,'x',4096);int64_t attempt=1;
    do{a=rt_process_input_write_some_v1(REF,META,1,++attempt,bytes,4096,0,4096);assert(word(a,0)==0&&word(a,1)==1);int64_t n=word(a,3);rt_array_free(a);if(n==0)break;assert(attempt<1024);}while(1);
    /* Same-thread held gate must refuse promptly, without consuming attempt
     * or acknowledging revoke. No concurrent-success claim is manufactured. */
    pthread_mutex_lock(&s_proc_lock);
    a=rt_process_input_write_some_v1(REF,META,1,attempt+1,"BAD",3,0,3);
    assert(word(a,0)==-7&&word(a,1)==0);rt_array_free(a);
    mutation(rt_process_input_revoke_v1(REF,META,1),-7);
    pthread_mutex_unlock(&s_proc_lock);
    a=rt_process_input_state_v1(REF);assert(word(a,2)==1&&word(a,5)==attempt&&word(a,6)==attempt);rt_array_free(a);
    mutation(rt_process_input_revoke_v1(REF,META,1),0);
    a=rt_process_input_write_some_v1(REF,META,1,attempt+1,"BAD",3,0,3);assert(word(a,0)==-12&&word(a,1)==0);rt_array_free(a);
    mutation(rt_process_input_install_v1(REF,META,1,expiry),-13);
    mutation(rt_process_input_install_v1(REF,META,2,expiry),0);
    a=rt_process_input_state_v1(REF);assert(word(a,3)==2&&word(a,5)==0&&word(a,6)==attempt&&word(a,10)==1&&word(a,7)==0);rt_array_free(a);
    while(read(input,bytes,sizeof(bytes))>0){}assert(errno==EAGAIN);
    a=rt_process_input_write_some_v1(REF,META,2,1,"Z",1,0,1);assert(word(a,1)==1&&word(a,3)==1);rt_array_free(a);
    assert(read(input,bytes,sizeof(bytes))==1&&bytes[0]=='Z');
    a=rt_process_input_write_some_v1(REF,META,2,2,"BAD",3,0,4097);assert(word(a,0)==-1&&word(a,1)==0);rt_array_free(a);
    a=rt_process_input_write_some_v1(REF,target,64,id,64,2,2,"BAD",3,0,3);assert(word(a,0)==-13&&word(a,1)==0);rt_array_free(a);
    /* Actual EPIPE has a known zero prefix, not Unknown; SIGPIPE is drained. */
    close(input);input=-1;
    a=rt_process_input_write_some_v1(REF,META,2,2,"BAD",3,0,3);assert(word(a,0)==-3&&word(a,1)==1&&word(a,3)==0);rt_array_free(a);
    assert(input_now_v1(&now));mutation(rt_process_input_install_v1(REF,META,3,now+1000000),0);
    struct timespec expired={0,2000000};nanosleep(&expired,NULL);
    a=rt_process_input_write_some_v1(REF,META,3,1,"BAD",3,0,3);assert(word(a,0)==-14&&word(a,1)==0);rt_array_free(a);
    a=rt_process_input_state_v1(REF);assert(word(a,3)==3&&word(a,5)==0&&word(a,6)==2&&word(a,10)==2);rt_array_free(a);
    /* Only TEST fixture teardown retires descriptors: no forged broker proof. */
    pthread_mutex_lock(&s_proc_lock);struct RtProcSlot* slot=stream_action_locked_v2(REF);assert(slot);proc_free_locked(slot);pthread_mutex_unlock(&s_proc_lock);
    int64_t old=generation;generation=rt_process_stream_reserve_v2();assert(generation>old);
    assert(rt_process_stream_bind_v2(generation,root,strlen(root),id,64)==0);
    mutation(rt_process_input_enable_v1(child,old,root,strlen(root),id,64),-2);
    mutation(rt_process_input_install_v1(child,old,root,strlen(root),id,64,META,9,expiry),-2);
    mutation(rt_process_input_revoke_v1(child,old,root,strlen(root),id,64,META,9),-2);
    a=rt_process_input_state_v1(child,old,root,strlen(root),id,64);assert(word(a,0)==-2);rt_array_free(a);
    pthread_mutex_lock(&s_proc_lock);
    struct RtProcSlot* replacement=stream_bound_locked_v2(generation,root,strlen(root),id,64);
    assert(replacement&&!replacement->input_controlled&&!replacement->input_active&&replacement->input_revision==0);
    pthread_mutex_unlock(&s_proc_lock);
    a=rt_process_input_write_some_v1(child,old,root,strlen(root),id,64,META,2,2,"BAD",3,0,3);assert(word(a,0)==-2&&word(a,1)==0);rt_array_free(a);
    assert(rt_process_stream_abandon_unlaunched_v2(generation,root,strlen(root),id,64)==0);
    assert(input==-1);assert(kill(child,SIGKILL)==0);int status;assert(waitpid(child,&status,0)==child&&WIFSIGNALED(status));
    assert(rmdir(root)==0);return 0;
}
#endif
