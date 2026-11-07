/* NEW transport-owner witness. Actual production registry/reader and real
 * descriptors/helper; no synthetic positive terminal lifecycle proof. Link
 * normal CoreC value providers. This is transport-only, not cgroup admission.
 */
#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE
#endif
#include "../runtime_process.c"
#include <assert.h>

#ifndef __linux__
int main(void) { return 77; } /* Explicit unsupported host, never a PASS. */
#else
static void tick(void) { struct timespec delay={0,1000000};nanosleep(&delay,NULL); }
static void write_file_at(int root,const char* name,const char* bytes) {
    int fd=openat(root,name,O_WRONLY|O_CREAT|O_EXCL|O_CLOEXEC|O_NOFOLLOW,0600);assert(fd>=0);
    assert(write(fd,bytes,strlen(bytes))==(ssize_t)strlen(bytes));assert(close(fd)==0);
}
int main(void) {
    alarm(20);
    char root[]="/tmp/simple-stream-transport-XXXXXX";assert(mkdtemp(root));
    const char* identity="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    const char* other="bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
    int64_t generation=rt_process_stream_reserve_v2();assert(generation>0);
    assert(rt_process_stream_bind_v2(generation,root,strlen(root),identity,64)==0);
    assert(rt_process_stream_bind_v2(generation,root,strlen(root),identity,64)==-2);
    int input=-1,output=-1,directory=-1;
    assert(rt_process_stream_claim_launch_v2(generation,root,strlen(root),other,64,&input,&output,&directory)==ESTALE);
    assert(rt_process_stream_claim_launch_v2(generation,root,strlen(root),identity,64,&input,&output,&directory)==0);
    assert(input>=6&&output>=6&&directory>=6);
    assert(fcntl(input,F_GETFD)&FD_CLOEXEC);assert(fcntl(output,F_GETFD)&FD_CLOEXEC);
    assert(rt_process_stream_abandon_unlaunched_v2(generation,root,strlen(root),identity,64)==-2);
    /* Known fork-not-started reset is narrow and makes the reservation releasable. */
    assert(rt_process_stream_launch_not_started_v2(generation,root,strlen(root),identity,64)==0);
    close(input);close(output);close(directory);
    assert(rt_process_stream_abandon_unlaunched_v2(generation,root,strlen(root),identity,64)==0);

    generation=rt_process_stream_reserve_v2();assert(generation>0);
    assert(rt_process_stream_bind_v2(generation,root,strlen(root),identity,64)==0);
    assert(rt_process_stream_claim_launch_v2(generation,root,strlen(root),identity,64,&input,&output,&directory)==0);
    pid_t child=fork();assert(child>=0);
    if(!child) {
        /* Test helper owns no group lifetime claim. It exercises actual moved
         * endpoints only; production pinned broker inheritance is separate. */
        alarm(10); /* Child owns an independent deadline even if parent fails. */
        assert(dup2(input,0)==0&&dup2(output,1)==1);
        assert(syscall(SYS_close_range,3U,~0U,0U)==0);
        char byte;assert(write(1,"stream",6)==6);
        assert(read(0,&byte,1)==1);assert(write(1,&byte,1)==1);
        _exit(0);
    }
    close(input);close(output);close(directory);
    assert(rt_process_stream_publish_broker_v2(generation,root,strlen(root),identity,64,child)==0);
    assert(rt_process_stream_pid_v2(generation,root,strlen(root),identity,64)==child);
    assert(rt_process_stream_abandon_unlaunched_v2(generation,root,strlen(root),identity,64)==-2);
    assert(rt_process_validate_piped_owned_v2(child,generation,root,strlen(root),identity,64)==0);
    assert(rt_process_validate_piped_ref_v1(child,generation)==-2);
    assert(rt_process_piped_pid_for_generation_v1(generation)==-2);
    assert(rt_process_stdout_state(child)==-1);
    struct SimplePipedObservationV1 observation;
    simple_piped_owner_observe_v1(child,1,&observation,sizeof(observation));
    assert(observation.owner_error!=0);
    SplArray* status=rt_process_piped_exit_status_value(child);
    assert(status&&rt_array_len(status)==4);
    assert(rt_value_as_int(rt_array_get(status,0))==1);
    assert(rt_value_as_int(rt_array_get(status,1))==-1);
    assert(rt_value_as_int(rt_array_get(status,3))==EINVAL);rt_array_free(status);
    assert(strcmp(rt_process_read_stdout(child),"")==0);
    assert(rt_process_write_stdin_some(child,"BAD",3,0,3)==-1);
    assert(!rt_process_is_alive(child));assert(!rt_process_close_piped(child));
    assert(rt_process_validate_piped_owned_v2(child,generation,root,strlen(root),other,64)==-2);
    assert(strcmp(rt_process_read_stdout_owned_v2(child,generation,root,strlen(root),other,64),"")==0);
    assert(rt_process_write_stdin_some_owned_v2(child,generation,root,strlen(root),other,64,"BAD",3,0,3)==-2);
    char bytes[32]={0};size_t used=0;
    for(int i=0;i<1000&&used<6;i++) {
        const char* chunk=rt_process_read_stdout_owned_v2(child,generation,root,strlen(root),identity,64);
        size_t count=strlen(chunk);assert(used+count<sizeof(bytes));memcpy(bytes+used,chunk,count+1);used+=count;
        if(used<6)tick();
    }
    assert(strcmp(bytes,"stream")==0);
    assert(rt_process_write_stdin_some_owned_v2(child,generation,root,strlen(root),identity,64,"X",1,0,1)==1);
    bool eof=false;
    for(int i=0;i<1000&&!eof;i++) {
        const char* chunk=rt_process_read_stdout_owned_v2(child,generation,root,strlen(root),identity,64);
        size_t count=strlen(chunk);assert(used+count<sizeof(bytes));memcpy(bytes+used,chunk,count+1);used+=count;
        eof=rt_process_stdout_state_owned_v2(child,generation,root,strlen(root),identity,64)==1;
        if(!eof)tick();
    }
    assert(eof&&strcmp(bytes,"streamX")==0);
    int child_status=0;assert(waitpid(child,&child_status,0)==child&&WIFEXITED(child_status)&&WEXITSTATUS(child_status)==0);
    /* A mutable pathname cannot replace the pinned root's proof authority. */
    char moved[4096];snprintf(moved,sizeof(moved),"%s-pinned",root);assert(rename(root,moved)==0);
    assert(mkdir(root,0700)==0);int replacement=open(root,O_RDONLY|O_DIRECTORY|O_CLOEXEC);assert(replacement>=0);
    const char* forged="SIMPLE-GROUP-STREAM-UNLAUNCHED-2\nforged\n";
    write_file_at(replacement,"broker.stream.unlaunched.sdn",forged);
    assert(rt_process_stream_retire_v2(generation,root,strlen(root),identity,64,forged,strlen(forged))==-1);
    assert(rt_process_validate_piped_owned_v2(child,generation,root,strlen(root),identity,64)==0);
    assert(unlinkat(replacement,"broker.stream.unlaunched.sdn",0)==0);close(replacement);assert(rmdir(root)==0);
    assert(rename(moved,root)==0);
    /* Explicit native TEST teardown of its known pipe/helper fixture. No
     * positive terminal proof or production lifecycle success is fabricated. */
    assert(pthread_mutex_lock(&s_proc_lock)==0);
    proc_free_locked(stream_ticket_locked_v2(generation));assert(pthread_mutex_unlock(&s_proc_lock)==0);
    assert(rt_process_validate_piped_owned_v2(child,generation,root,strlen(root),identity,64)==-2);
    assert(rt_process_stream_retire_v2(generation,root,strlen(root),identity,64,forged,strlen(forged))==-2);
    int64_t replacement_generation=rt_process_stream_reserve_v2();
    assert(replacement_generation>generation);
    assert(rt_process_stream_bind_v2(replacement_generation,root,strlen(root),identity,64)==0);
    assert(pthread_mutex_lock(&s_proc_lock)==0);
    assert(stream_bound_locked_v2(replacement_generation,root,strlen(root),identity,64));
    assert(!stream_bound_locked_v2(generation,root,strlen(root),identity,64));
    assert(pthread_mutex_unlock(&s_proc_lock)==0);
    assert(rt_process_validate_piped_owned_v2(child,generation,root,strlen(root),identity,64)==-2);
    assert(rt_process_stream_abandon_unlaunched_v2(replacement_generation,root,strlen(root),identity,64)==0);
    assert(rmdir(root)==0);
    puts("PASS transport-only: bound ticket/reader, actual endpoints, raw denial, pinned-root refusal");
    return 0;
}
#endif
