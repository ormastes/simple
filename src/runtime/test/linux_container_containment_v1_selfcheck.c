/* AUTHORED_UNRUN. Link real Core-C plus --wrap=close. No namespace/cgroup
 * provisioning and no positive containment fixture. Wrong path and same-namespace
 * captures must preserve partial owners; this is not an empty-group proof. */
#define _GNU_SOURCE
#include "runtime.h"
#include "runtime_workspace_storage_v1.h"
#include "../runtime_linux_cgroup_events_private.h"
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/wait.h>
static unsigned checks;
#define CHECK(x) do {checks++;if(!(x)){fprintf(stderr,"check %u line %d failed\n",checks,__LINE__);return 1;}}while(0)
static int fail_close_once,close_faults;
int __real_close(int fd);
int __wrap_close(int fd){int result=__real_close(fd);if(fail_close_once){fail_close_once=0;close_faults++;errno=EINTR;return -1;}return result;}
static int64_t text(const char* s){return rt_string_new((const uint8_t*)s,strlen(s));}
int main(void){
#if !defined(__linux__)
    fprintf(stderr,"Linux containment native owner required\n");return 77;
#else
    int populated=-1;
    CHECK(rt_lg_parse_populated("populated 1\nfrozen 0\n",21,&populated)&&populated==1);
    CHECK(rt_lg_parse_populated("populated 0\n",12,&populated)&&populated==0);
    CHECK(!rt_lg_parse_populated("populated 0",11,&populated));
    CHECK(!rt_lg_parse_populated("populated 0\npopulated 0\n",24,&populated));
    CHECK(!rt_lg_parse_populated("populated 0\nunknown 0\n",22,&populated));
    const int64_t binding=text("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
    const int64_t other=text("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb");
    CHECK(rt_linux_container_containment_capture_v1(0,text("/unrelated"),binding)<0);
    CHECK(rt_linux_container_containment_capture_v1(getpid(),text("/../escape"),binding)<0);
    CHECK(rt_linux_container_containment_capture_v1(getpid(),text("/unrelated"),text("bad"))<0);
    int gate[2];CHECK(pipe(gate)==0);pid_t child=fork();CHECK(child>=0);
    if(!child){close(gate[1]);char byte;if(read(gate[0],&byte,1)!=1)_exit(18);_exit(17);}
    close(gate[0]);
    int64_t token=rt_linux_container_containment_capture_v1(child,text("/not-the-child-cgroup"),binding);
    CHECK(token>0);
    CHECK(rt_string_len(rt_linux_container_containment_observe_v1(token,binding))==0);
    CHECK(rt_linux_container_containment_close_v1(token,other)<0);
    CHECK(rt_string_len(rt_linux_container_user_observe_v1(token,binding))==0);
    CHECK(rt_linux_container_user_close_v1(token,binding)<0);
    CHECK(rt_linux_container_containment_close_v1(token,binding)==0);
    CHECK(rt_linux_container_containment_close_v1(token,binding)<0);
    int status=0;CHECK(waitpid(child,&status,WNOHANG)==0);
    CHECK(write(gate[1],"x",1)==1);close(gate[1]);
    CHECK(waitpid(child,&status,0)==child&&WIFEXITED(status)&&WEXITSTATUS(status)==17);
    token=rt_linux_container_containment_capture_v1(getpid(),text("/not-the-current-cgroup"),binding);
    CHECK(token>0);fail_close_once=1;
    CHECK(rt_linux_container_containment_close_v1(token,binding)<0&&close_faults==1);
    CHECK(rt_linux_container_containment_close_v1(token,binding)<0&&close_faults==1);
    CHECK(rt_string_len(rt_linux_container_containment_observe_v1(token,binding))==0);
    printf("containment negative owner checks=%u; no positive containment qualification\n",checks);
    return 0;
#endif
}
