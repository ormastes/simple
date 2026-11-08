/* EXTERNAL peer protocol: invoke server/client separately under ALREADY
 * provisioned distinct UIDs. Never creates users, forks peers, changes identity
 * or elevates privilege. Parent path provisioning is outside this harness. */
#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE
#endif
#include "../runtime_socket_nonblock.c"
#include <assert.h>
#if !defined(__linux__)
int main(void){return 77;}
#else
static int64_t ew(SplArray* a,int i){assert(a&&rt_array_len(a)>i);return rt_value_as_int(rt_array_get(a,i));}
static int64_t uid_argument(const char* source) {
    char* end=NULL;errno=0;unsigned long value=strtoul(source,&end,10);
    if(errno||!end||*end||end==source||value>UINT32_MAX)return -1;
    return (int64_t)value;
}
/* Test-only readiness wait, no bytes read outside the production recvmsg owner. */
static void await_readable(int64_t token) {
    int status;LuSlotV1* slot=lu_lock_v1(token,&status);assert(slot&&status==0);
    struct pollfd p={.fd=slot->fd,.events=POLLIN};int rc=poll(&p,1,5000);
    pthread_mutex_unlock(&slot->operation);assert(rc>0&&!(p.revents&POLLNVAL));
}
static int server(const char* path,int64_t client_uid) {
    if(client_uid==(int64_t)geteuid())return 2;
    SplArray* a=rt_local_unix_listen_v1(path,strlen(path),geteuid(),8);
    assert(ew(a,0)==0);int64_t listener=ew(a,1);assert(listener>0);rt_array_free(a);
    printf("READY external-peer socket=%s service_uid=%lu expected_client_uid=%lld\n",path,(unsigned long)geteuid(),(long long)client_uid);fflush(stdout);
    await_readable(listener);
    a=rt_local_unix_accept_v1(listener,client_uid);assert(ew(a,0)==0&&ew(a,2)==client_uid);
    int64_t connection=ew(a,1);assert(connection>0);rt_array_free(a);
    a=rt_local_unix_peer_v1(connection);assert(ew(a,0)==0&&ew(a,1)==client_uid&&ew(a,3)>0);rt_array_free(a);
    const char* request="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    a=rt_local_unix_claim_request_v1(connection,request,64);assert(ew(a,0)==-13&&!ew(a,1));rt_array_free(a);
    await_readable(connection);
    a=rt_local_unix_read_now_v1(connection,16);assert(ew(a,0)==0&&ew(a,2)==1&&ew(a,3)=='R');rt_array_free(a);
    await_readable(connection);
    a=rt_local_unix_read_now_v1(connection,16);assert(ew(a,0)==0&&ew(a,1)==1&&ew(a,2)==0);rt_array_free(a);
    a=rt_local_unix_claim_request_v1(connection,request,64);assert(ew(a,0)==0&&ew(a,1)==1);rt_array_free(a);
    a=rt_local_unix_claim_request_v1(connection,request,64);assert(ew(a,0)==-14&&!ew(a,1));rt_array_free(a);
    a=rt_local_unix_claim_request_v1(connection,"bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",64);assert(ew(a,0)==-14&&!ew(a,1));rt_array_free(a);
    a=rt_local_unix_close_v1(connection);assert(ew(a,1)==1);rt_array_free(a);
    a=rt_local_unix_listener_close_v1(listener);assert(ew(a,1)==1);rt_array_free(a);
    puts("PASS external actual distinct-UID accept/peer/observed-EOF one-use request phase");return 0;
}
static int client(const char* path,int64_t service_uid) {
    if(service_uid==(int64_t)geteuid())return 2;
    SplArray* a=rt_local_unix_connect_v1(path,strlen(path),service_uid,lu_clock_v1(CLOCK_MONOTONIC)+1000);
    assert(ew(a,0)==0&&ew(a,2)==service_uid);int64_t token=ew(a,1);assert(token>0);rt_array_free(a);
    SplArray* bytes=lu_receipt_v1(1);assert(bytes);lu_word_v1(bytes,0,'R');
    a=rt_local_unix_write_some_now_v1(token,bytes,0,1);assert(ew(a,0)==0&&ew(a,1)==1);rt_array_free(a);rt_array_free(bytes);
    a=rt_local_unix_shutdown_write_v1(token);assert(ew(a,0)==0&&ew(a,1)==1);rt_array_free(a);
    a=rt_local_unix_close_v1(token);assert(ew(a,1)==1);rt_array_free(a);
    puts("PASS external client submitted one byte then actual write EOF");return 0;
}
int main(int argc,char** argv) {
    alarm(12);
    if(argc!=4){fprintf(stderr,"usage: external-peer (--server|--client) SOCKET_PATH EXPECTED_OTHER_UID\n");return 2;}
    int64_t uid=uid_argument(argv[3]);if(uid<0)return 2;
    if(!strcmp(argv[1],"--server"))return server(argv[2],uid);
    if(!strcmp(argv[1],"--client"))return client(argv[2],uid);
    return 2;
}
#endif
