/* Read-only external primary-task observation. No signal, wait, adoption or
 * namespace entry. A pidfd is pinned before any numeric /proc lookup. */
#ifndef SIMPLE_WORKSPACE_USER_OBSERVATION_LINUX_PRIVATE_H
#define SIMPLE_WORKSPACE_USER_OBSERVATION_LINUX_PRIVATE_H
#include <poll.h>
#include <time.h>
#include <linux/nsfs.h>
#include <sched.h>
#include "runtime_process_owned_sha256_private.h"

#define WS_MAP_BYTES_V1 65536
#define WS_MAP_RANGES_V1 64
typedef struct { uint64_t inside,outside,count; } WsIdRangeV1;
typedef struct {
    uint64_t start_ticks,target_ns_device,target_ns_inode,observer_ns_device,observer_ns_inode;
    uint32_t observer_uid,observer_gid,effective_uid,effective_gid,filesystem_uid,filesystem_gid;
    uint32_t container_uid,container_gid;
    char cgroup[4096],uid_digest[65],gid_digest[65];
} WsUserFactsV1;
typedef struct {
    int pidfd,procfd,usernsfd,observernsfd,observer_procfd;
    pid_t pid;
    uint32_t overflow_uid,overflow_gid;
    WsUserFactsV1 facts;
} WsUserNativeV1;

static int ws_proc_read_v1(int directory,const char* name,char* output,size_t capacity) {
    int fd=openat(directory,name,O_RDONLY|O_CLOEXEC|O_NOFOLLOW);
    if(fd<0)return errno;
    size_t used=0;int error=0;
    while(used<capacity-1) {
        ssize_t got=read(fd,output+used,capacity-1-used);
        if(got<0){error=errno;break;}if(!got)break;used+=(size_t)got;
    }
    if(!error&&used==capacity-1){char extra;ssize_t got=read(fd,&extra,1);if(got!=0)error=got<0?errno:EOVERFLOW;}
    close(fd);output[used]=0;
    if(!error&&(!used||memchr(output,0,used)))error=EINVAL;
    return error;
}
static int ws_decimal_v1(const char** cursor,uint64_t maximum,uint64_t* value) {
    const char* p=*cursor;while(*p==' '||*p=='\t')p++;
    if(*p<'0'||*p>'9')return EINVAL;
    uint64_t result=0;
    do {unsigned d=(unsigned)(*p-'0');if(result>(maximum-d)/10)return EOVERFLOW;result=result*10+d;p++;}
    while(*p>='0'&&*p<='9');
    if(result>maximum)return EOVERFLOW;*value=result;*cursor=p;return 0;
}
static int ws_line_numbers_v1(const char* bytes,const char* key,uint64_t* out,size_t count) {
    const char* found=NULL;size_t key_size=strlen(key);
    for(const char* p=bytes;*p;) {
        if(!strncmp(p,key,key_size)){if(found)return EINVAL;found=p+key_size;}
        const char* end=strchr(p,'\n');if(!end)return EINVAL;p=end+1;
    }
    if(!found)return ENOTSUP;
    for(size_t i=0;i<count;i++){int error=ws_decimal_v1(&found,UINT32_MAX-1,&out[i]);if(error)return error;}
    while(*found==' '||*found=='\t')found++;
    return *found=='\n'?0:EINVAL;
}
static int ws_proc_status_v1(int proc,pid_t pid,uint32_t* effective_uid,uint32_t* effective_gid,
        uint32_t* filesystem_uid,uint32_t* filesystem_gid,int observer) {
    char status[WS_MAP_BYTES_V1+1];int error=ws_proc_read_v1(proc,"status",status,sizeof(status));if(error)return error;
    uint64_t ids[4],one[1];
    error=ws_line_numbers_v1(status,"Pid:",one,1);if(error||one[0]!=(uint64_t)pid)return ESTALE;
    error=ws_line_numbers_v1(status,"Tgid:",one,1);if(error||one[0]!=(uint64_t)(observer?getpid():pid))return ESTALE;
    /* A procfs from an ancestor PID namespace has multiple NSpid columns.
     * Require this proc mount to use the observer's current PID namespace. */
    if(observer){error=ws_line_numbers_v1(status,"NSpid:",one,1);if(error||one[0]!=(uint64_t)pid)return ENOTSUP;}
    error=ws_line_numbers_v1(status,"Uid:",ids,4);if(error)return error;
    *effective_uid=(uint32_t)ids[1];*filesystem_uid=(uint32_t)ids[3];
    error=ws_line_numbers_v1(status,"Gid:",ids,4);if(error)return error;
    *effective_gid=(uint32_t)ids[1];*filesystem_gid=(uint32_t)ids[3];return 0;
}
static int ws_proc_start_v1(int proc,pid_t pid,uint64_t* ticks) {
    char stat[4096];int error=ws_proc_read_v1(proc,"stat",stat,sizeof(stat));if(error)return error;
    const char* p=stat;uint64_t observed;error=ws_decimal_v1(&p,INT_MAX,&observed);
    if(error||observed!=(uint64_t)pid||p[0]!=' '||p[1]!='(')return ESTALE;
    p=strrchr(p,')');if(!p||p[1]!=' '||!p[2]||p[3]!=' ')return EINVAL;
    if(p[2]=='Z'||p[2]=='X'||p[2]=='x')return ESRCH;p+=4;
    /* Fields 4..21 may be signed. Skip precisely bounded complete tokens. */
    for(int field=4;field<22;field++) {
        const char* start=p;if(*p=='-')p++;
        while(*p>='0'&&*p<='9')p++;
        if(p==start||(p==start+1&&start[0]=='-')||*p!=' ')return EINVAL;p++;
    }
    error=ws_decimal_v1(&p,INT64_MAX,ticks);
    return error?error:(!*ticks||(*p!=' '&&*p!='\n')?EINVAL:0);
}
static int ws_pidfd_live_v1(int fd) {
    struct pollfd item={.fd=fd,.events=POLLIN};int result=poll(&item,1,0);
    return result<0?errno:result==0?0:ESRCH;
}
static int ws_userns_identity_v1(int fd,uint64_t* device,uint64_t* inode) {
    struct stat value;struct statfs fs;
    if(fstat(fd,&value)||fstatfs(fd,&fs))return errno;
    if(fs.f_type!=NSFS_MAGIC||ioctl(fd,NS_GET_NSTYPE)!=CLONE_NEWUSER)return ENOTSUP;
    *device=(uint64_t)value.st_dev;*inode=(uint64_t)value.st_ino;return 0;
}
static int ws_current_userns_v1(int proc,uint64_t* device,uint64_t* inode) {
    /* This kernel-owned magic link is intentionally followed, unlike paths
     * supplied by callers. The retained procdir prevents numeric PID reuse. */
    int fd=openat(proc,"ns/user",O_RDONLY|O_CLOEXEC);if(fd<0)return errno;
    int error=ws_userns_identity_v1(fd,device,inode);close(fd);return error;
}
static void ws_map_digest_v1(const char* bytes,char out[65]) {
    uint8_t hash[32];owned_sha256((const uint8_t*)bytes,strlen(bytes),hash);
    static const char hex[]="0123456789abcdef";
    for(size_t i=0;i<32;i++){out[i*2]=hex[hash[i]>>4];out[i*2+1]=hex[hash[i]&15];}out[64]=0;
}
static int ws_inverse_map_v1(int proc,const char* name,uint32_t observed,int same_namespace,
        uint32_t* container,char digest[65]) {
    char bytes[WS_MAP_BYTES_V1+1];int error=ws_proc_read_v1(proc,name,bytes,sizeof(bytes));if(error)return error;
    WsIdRangeV1 ranges[WS_MAP_RANGES_V1];size_t count=0;const char* p=bytes;
    while(*p) {
        if(count==WS_MAP_RANGES_V1)return EOVERFLOW;
        WsIdRangeV1 range;
        if((error=ws_decimal_v1(&p,UINT32_MAX-1,&range.inside))||
           (error=ws_decimal_v1(&p,UINT32_MAX-1,&range.outside))||
           (error=ws_decimal_v1(&p,UINT32_MAX,&range.count)))return error;
        while(*p==' '||*p=='\t')p++;
        if(*p!='\n'||!range.count||range.inside+range.count>UINT64_C(4294967296)||
                range.outside+range.count>UINT64_C(4294967296))return EINVAL;p++;
        for(size_t i=0;i<count;i++)if((range.inside<ranges[i].inside+ranges[i].count&&ranges[i].inside<range.inside+range.count)||
                (range.outside<ranges[i].outside+ranges[i].count&&ranges[i].outside<range.outside+range.count))return EINVAL;
        ranges[count++]=range;
    }
    if(!count)return ENOTSUP;
    if(same_namespace)*container=observed;
    else {
        unsigned matches=0;uint64_t found=0;
        for(size_t i=0;i<count;i++)if(observed>=ranges[i].outside&&observed-ranges[i].outside<ranges[i].count){matches++;found=ranges[i].inside+(observed-ranges[i].outside);}
        if(matches!=1||found>=UINT32_MAX)return ENOTSUP;*container=(uint32_t)found;
    }
    ws_map_digest_v1(bytes,digest);return 0;
}
static int ws_cgroup_path_v1(const char* path) {
    size_t size=strlen(path);if(size<2||size>4095||path[0]!='/'||path[size-1]=='/'||strstr(path,"//"))return 0;
    for(const char* p=path;*p;p++)if((unsigned char)*p<32||*p=='\\')return 0;
    const char* p=path+1;
    while(*p){const char* end=strchr(p,'/');size_t n=end?(size_t)(end-p):strlen(p);if((n==1&&p[0]=='.')||(n==2&&p[0]=='.'&&p[1]=='.'))return 0;if(!end)break;p=end+1;}
    return 1;
}
static int ws_proc_cgroup_v1(int proc,char output[4096]) {
    char bytes[8192];int error=ws_proc_read_v1(proc,"cgroup",bytes,sizeof(bytes));if(error)return error;
    if(strncmp(bytes,"0::",3))return ENOTSUP;
    char* end=strchr(bytes,'\n');if(!end||end[1])return ENOTSUP;*end=0;
    if(!ws_cgroup_path_v1(bytes+3))return ENOTSUP;strcpy(output,bytes+3);return 0;
}
static int ws_user_snapshot_v1(WsUserNativeV1* native,const char* expected,WsUserFactsV1* facts) {
    memset(facts,0,sizeof(*facts));int error=ws_pidfd_live_v1(native->pidfd);if(error)return error;
    uint32_t observer_fsuid,observer_fsgid;
    error=ws_proc_status_v1(native->observer_procfd,(pid_t)syscall(SYS_gettid),&facts->observer_uid,&facts->observer_gid,&observer_fsuid,&observer_fsgid,1);if(error)return error;
    if(facts->observer_uid!=(uint32_t)geteuid()||facts->observer_gid!=(uint32_t)getegid()||
            facts->observer_uid!=observer_fsuid||facts->observer_gid!=observer_fsgid)return ESTALE;
    error=ws_proc_status_v1(native->procfd,native->pid,&facts->effective_uid,&facts->effective_gid,&facts->filesystem_uid,&facts->filesystem_gid,0);if(error)return error;
    if(facts->effective_uid==native->overflow_uid||facts->filesystem_uid==native->overflow_uid||
            facts->effective_gid==native->overflow_gid||facts->filesystem_gid==native->overflow_gid)return ENOTSUP;
    error=ws_proc_start_v1(native->procfd,native->pid,&facts->start_ticks);if(error)return error;
    error=ws_current_userns_v1(native->procfd,&facts->target_ns_device,&facts->target_ns_inode);if(error)return error;
    error=ws_current_userns_v1(native->observer_procfd,&facts->observer_ns_device,&facts->observer_ns_inode);if(error)return error;
    uint64_t dev,ino;
    error=ws_userns_identity_v1(native->usernsfd,&dev,&ino);if(error||dev!=facts->target_ns_device||ino!=facts->target_ns_inode)return ESTALE;
    error=ws_userns_identity_v1(native->observernsfd,&dev,&ino);if(error||dev!=facts->observer_ns_device||ino!=facts->observer_ns_inode)return ESTALE;
    int same=facts->target_ns_device==facts->observer_ns_device&&facts->target_ns_inode==facts->observer_ns_inode;
    error=ws_inverse_map_v1(native->procfd,"uid_map",facts->effective_uid,same,&facts->container_uid,facts->uid_digest);if(error)return error;
    error=ws_inverse_map_v1(native->procfd,"gid_map",facts->effective_gid,same,&facts->container_gid,facts->gid_digest);if(error)return error;
    error=ws_proc_cgroup_v1(native->procfd,facts->cgroup);if(error)return error;
    if(strcmp(expected,facts->cgroup))return ESTALE;
    return ws_pidfd_live_v1(native->pidfd);
}
static void ws_user_close_v1(WsUserNativeV1* native) {
    if(native->pidfd>=0)close(native->pidfd);if(native->procfd>=0)close(native->procfd);
    if(native->usernsfd>=0)close(native->usernsfd);if(native->observernsfd>=0)close(native->observernsfd);
    if(native->observer_procfd>=0)close(native->observer_procfd);
    native->pidfd=native->procfd=native->usernsfd=native->observernsfd=native->observer_procfd=-1;
}
static int ws_user_open_v1(WsUserNativeV1* native,pid_t pid,const char* expected) {
    memset(native,0,sizeof(*native));native->pid=pid;
    native->pidfd=native->procfd=native->usernsfd=native->observernsfd=native->observer_procfd=-1;
    if(!ws_cgroup_path_v1(expected))return EINVAL;
#ifdef SYS_pidfd_open
    native->pidfd=(int)syscall(SYS_pidfd_open,pid,0);
#else
    return ENOTSUP;
#endif
    if(native->pidfd<0)return errno;
    int error=ws_pidfd_live_v1(native->pidfd);if(error)return error;
    int proc=open("/proc",O_RDONLY|O_DIRECTORY|O_CLOEXEC|O_NOFOLLOW);if(proc<0)return errno;
    struct statfs fs;if(fstatfs(proc,&fs)||fs.f_type!=PROC_SUPER_MAGIC){close(proc);return ENOTSUP;}
    char name[32];snprintf(name,sizeof(name),"%ld",(long)pid);
    native->procfd=openat(proc,name,O_RDONLY|O_DIRECTORY|O_CLOEXEC|O_NOFOLLOW);
    /* FSUID is thread-local. Retain the actual calling thread, not the TGID
     * leader's status; another thread may not consume this observation. */
    native->observer_procfd=openat(proc,"thread-self",O_RDONLY|O_DIRECTORY|O_CLOEXEC);
    char overflow[64];
    error=ws_proc_read_v1(proc,"sys/kernel/overflowuid",overflow,sizeof(overflow));
    const char* cursor=overflow;uint64_t number=0;
    if(!error)error=ws_decimal_v1(&cursor,UINT32_MAX-1,&number);native->overflow_uid=(uint32_t)number;
    if(!error)error=ws_proc_read_v1(proc,"sys/kernel/overflowgid",overflow,sizeof(overflow));
    cursor=overflow;if(!error)error=ws_decimal_v1(&cursor,UINT32_MAX-1,&number);native->overflow_gid=(uint32_t)number;
    close(proc);if(error)return error;if(native->procfd<0||native->observer_procfd<0)return EACCES;
    native->usernsfd=openat(native->procfd,"ns/user",O_RDONLY|O_CLOEXEC);
    native->observernsfd=openat(native->observer_procfd,"ns/user",O_RDONLY|O_CLOEXEC);
    if(native->usernsfd<0||native->observernsfd<0)return errno;
    WsUserFactsV1 first,second;
    error=ws_user_snapshot_v1(native,expected,&first);if(error)return error;
    error=ws_user_snapshot_v1(native,expected,&second);if(error)return error;
    if(memcmp(&first,&second,sizeof(first)))return ESTALE;
    native->facts=second;return 0;
}
static int ws_user_refresh_v1(WsUserNativeV1* native,const char* expected) {
    WsUserFactsV1 first,second;int error=ws_user_snapshot_v1(native,expected,&first);if(error)return error;
    error=ws_user_snapshot_v1(native,expected,&second);if(error)return error;
    if(memcmp(&first,&second,sizeof(first))||memcmp(&first,&native->facts,sizeof(first)))return ESTALE;
    return 0;
}
#endif
