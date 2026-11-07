/* Real negative native-owner regression. No injected quota-success facts.
 * Positive enforcement requires a separate administrator-provisioned fixture. */
#define _GNU_SOURCE
#include "runtime.h"
#include "runtime_workspace_storage_v1.h"
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>
#include <dirent.h>

static unsigned checks;
#define CHECK(x) do { checks++; if(!(x)){fprintf(stderr,"FAIL:%d:%s\n",__LINE__,#x);abort();} } while(0)
static int64_t value(const char* s){return rt_string_new((const uint8_t*)s,strlen(s));}
static int descriptor_count(void) {
    DIR* d=opendir("/proc/self/fd");if(!d)return -1;int n=0;
    while(readdir(d))n++;closedir(d);return n;
}
int main(void) {
#if defined(__linux__)
    char parent[]="/tmp/simple-storage-native-XXXXXX";CHECK(mkdtemp(parent)!=NULL);
    char child[4096],sentinel[4096],link[4096];
    CHECK(snprintf(child,sizeof(child),"%s/workspace",parent)>0);
    CHECK(snprintf(sentinel,sizeof(sentinel),"%s/keep",child)>0);
    CHECK(snprintf(link,sizeof(link),"%s/alias",parent)>0);
    CHECK(mkdir(child,0700)==0);
    FILE* file=fopen(sentinel,"w");CHECK(file!=NULL);CHECK(fputs("dirty-must-survive",file)>=0);CHECK(fclose(file)==0);
    CHECK(symlink(child,link)==0);
    struct stat before,after;CHECK(stat(child,&before)==0);
    int initial=descriptor_count();CHECK(initial>0);
    const char* digest="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    int64_t kind=value("linux-xfs-project-v1"),p=value(parent),leaf=value("workspace");
    int64_t pool=value("xfs:deliberately-wrong"),workspace=value("inode:deliberately-wrong"),policy=value(digest);
    for(int i=0;i<40;i++) {
        CHECK(rt_workspace_storage_open_v1(kind,p,leaf,pool,workspace,77,65536,policy)<0);
    }
    CHECK(descriptor_count()==initial);
    CHECK(rt_workspace_storage_open_v1(kind,p,value("../workspace"),pool,workspace,77,65536,policy)==-EINVAL);
    CHECK(rt_workspace_storage_open_v1(kind,p,value("alias"),pool,workspace,77,65536,policy)<0);
    CHECK(rt_workspace_storage_open_v1(value("invented-provider"),p,leaf,pool,workspace,77,65536,policy)<0);
    CHECK(rt_workspace_storage_open_v1(kind,p,leaf,pool,workspace,77,-1,policy)==-EINVAL);
    CHECK(rt_workspace_storage_open_v1(kind,p,leaf,pool,workspace,77,65536,value("bad-policy"))==-EINVAL);
    CHECK(rt_workspace_storage_recover_v1(kind,p,leaf,pool,workspace,77,65536,policy)<0);
    CHECK(rt_workspace_storage_release_if_absent_v1(1)==-ESTALE);
    CHECK(rt_workspace_storage_forget_released_v1(1)==-ESTALE);
    CHECK(rt_string_len(rt_workspace_storage_observe_v1(1))==0);
    CHECK(stat(child,&after)==0);CHECK(before.st_ino==after.st_ino);CHECK(before.st_mode==after.st_mode);
    file=fopen(sentinel,"r");CHECK(file!=NULL);char retained[64]={0};CHECK(fread(retained,1,sizeof(retained)-1,file)==18);
    CHECK(fclose(file)==0);CHECK(strcmp(retained,"dirty-must-survive")==0);
    CHECK(descriptor_count()==initial);
    CHECK(unlink(link)==0);CHECK(unlink(sentinel)==0);CHECK(rmdir(child)==0);CHECK(rmdir(parent)==0);
    printf("PASS workspace storage negative native owner: %u checks; real filesystem, unsupported/mismatch refusal, dirty preservation, no leaked descriptors\n",checks);
    return 0;
#else
    fputs("UNSUPPORTED: this negative filesystem fixture requires Linux\n",stderr);return 77;
#endif
}
