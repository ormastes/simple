/* Observation only. No process control, migration, removal or discharge.
 * Every opened descriptor belongs to the published role-3 registry slot. */
#ifndef SIMPLE_WORKSPACE_CONTAINMENT_LINUX_PRIVATE_H
#define SIMPLE_WORKSPACE_CONTAINMENT_LINUX_PRIVATE_H
#include "runtime_linux_cgroup_events_private.h"
#define WS_CONTAIN_FDS_V1 96
#define WS_CONTAIN_MOUNTS_V1 262144
#define WS_CONTAIN_PROCS_V1 65536

typedef struct {
    int fds[WS_CONTAIN_FDS_V1], count, error, close_uncertain, captured;
    int pidfd, procfd, observerfd, mountfd, groupfd, eventsfd, mountinfofd, statfd, cgroupfd;
    int link_count, link_parent[64], link_child[64];
    char link_name[64][256];
    int namespaces[5]; /* target pid/cgroup, observer pid/cgroup/mount */
    uint64_t ns_device[5], ns_inode[5];
    uint64_t start_ticks, mount_id, mount_device, mount_inode, group_device, group_inode;
    pid_t pid;
    pid_t kernel_tid;
    int kernel_rootfd, kernel_sysfsfd, kernel_dirfd, kernel_notesfd, kernel_statusfd;
    char path[4096], mountpoint[4096];
} WsContainNativeV1;

static void ws_contain_init_v1(WsContainNativeV1* n) {
    memset(n,0,sizeof(*n));
    for(size_t i=0;i<WS_CONTAIN_FDS_V1;i++)n->fds[i]=-1;
    n->kernel_rootfd=n->kernel_sysfsfd=n->kernel_dirfd=n->kernel_notesfd=n->kernel_statusfd=-1;
}
static int ws_contain_keep_v1(WsContainNativeV1* n,int fd) {
    /* Callers reserve room before the syscall; never discard an opened FD. */
    if(fd<0)return -1;
    n->fds[n->count++]=fd;return fd;
}
static int ws_contain_openat_v1(WsContainNativeV1* n,int parent,const char* name,int flags) {
    if(n->count==WS_CONTAIN_FDS_V1){errno=ENOSPC;return -1;}
    return ws_contain_keep_v1(n,openat(parent,name,flags|O_CLOEXEC));
}
static int ws_contain_read_v1(int fd,char* bytes,size_t capacity) {
    size_t used=0;
    while(used<capacity-1) {
        ssize_t got=pread(fd,bytes+used,capacity-1-used,(off_t)used);
        if(got<0)return errno;if(!got)break;used+=(size_t)got;
    }
    if(used==capacity-1){char extra;ssize_t got=pread(fd,&extra,1,(off_t)used);if(got)return got<0?errno:EOVERFLOW;}
    if(!used||memchr(bytes,0,used))return EINVAL;bytes[used]=0;return 0;
}
static int ws_contain_ns_v1(int fd,int type,uint64_t* device,uint64_t* inode) {
    struct stat st;struct statfs fs;
    if(fstat(fd,&st)||fstatfs(fd,&fs))return errno;
    if(fs.f_type!=NSFS_MAGIC||ioctl(fd,NS_GET_NSTYPE)!=type)return ENOTSUP;
    if((uint64_t)st.st_dev>INT64_MAX||(uint64_t)st.st_ino>INT64_MAX||!st.st_ino)return EOVERFLOW;
    *device=(uint64_t)st.st_dev;*inode=(uint64_t)st.st_ino;return 0;
}
static int ws_contain_namespaces_v1(WsContainNativeV1* n,int capture) {
    const char* names[]={"ns/pid","ns/cgroup","ns/pid","ns/cgroup","ns/mnt"};
    const int types[]={CLONE_NEWPID,CLONE_NEWCGROUP,CLONE_NEWPID,CLONE_NEWCGROUP,CLONE_NEWNS};
    for(size_t i=0;i<5;i++) {
        if(!capture&&i<2)continue; /* Primary may have died; pins remain. */
        int proc=i<2?n->procfd:n->observerfd;
        if(capture==1) {
            n->namespaces[i]=ws_contain_openat_v1(n,proc,names[i],O_RDONLY);
            if(n->namespaces[i]<0)return errno;
            int e=ws_contain_ns_v1(n->namespaces[i],types[i],&n->ns_device[i],&n->ns_inode[i]);if(e)return e;
        }
        struct stat current;
        /* Observer identity must describe the calling thread, not a retained
         * departed thread. Kernel magic links are intentionally followed. */
        char path[96];snprintf(path,sizeof(path),"/proc/thread-self/%s",names[i]);
        int result=i<2?fstatat(proc,names[i],&current,0):stat(path,&current);
        if(result)return errno;
        if((uint64_t)current.st_dev!=n->ns_device[i]||(uint64_t)current.st_ino!=n->ns_inode[i])return ESTALE;
    }
    if(capture&&(n->ns_device[0]==n->ns_device[2]&&n->ns_inode[0]==n->ns_inode[2]))return ENOTSUP;
    if(capture&&(n->ns_device[1]==n->ns_device[3]&&n->ns_inode[1]==n->ns_inode[3]))return ENOTSUP;
    return 0;
}
/* One visible cgroup2 mount, filesystem root '/', no namespace-root guessing.
 * The actual target PID membership below independently checks the projection. */
static int ws_contain_mount_v1(WsContainNativeV1* n,int capture) {
    char* bytes=malloc(WS_CONTAIN_MOUNTS_V1+1);if(!bytes)return ENOMEM;
    int error=ws_contain_read_v1(n->mountinfofd,bytes,WS_CONTAIN_MOUNTS_V1+1);
    size_t rows=0,selected=0;uint64_t id=0;unsigned maj=0,min=0;char point[4096]={0};
    for(char* row=bytes;!error&&*row;) {
        if(++rows>512){error=EOVERFLOW;break;}
        char* end=strchr(row,'\n');if(!end){error=EINVAL;break;}*end=0;
        char* fields[128];size_t count=0;
        for(char* p=row;*p;) {
            if(count==128){error=EOVERFLOW;break;}fields[count++]=p;
            char* space=strchr(p,' ');if(!space)break;*space=0;p=space+1;if(!*p||*p==' '){error=EINVAL;break;}
        }
        if(error)break;if(count<10){error=EINVAL;break;}
        size_t sep=6;while(sep<count&&strcmp(fields[sep],"-"))sep++;
        if(sep+4!=count){error=EINVAL;break;}
        if(!strcmp(fields[sep+1],"cgroup2")) {
            uint64_t number=0;
            if(++selected!=1||strcmp(fields[3],"/")){error=ENOTSUP;break;}
            error=ws_prep_unsigned_v1(fields[0],INT64_MAX,&id);
            if(error||!id){error=EINVAL;break;}
            char* colon=strchr(fields[2],':');if(!colon){error=EINVAL;break;}*colon=0;
            error=ws_prep_unsigned_v1(fields[2],UINT_MAX,&number);maj=(unsigned)number;
            if(!error)error=ws_prep_unsigned_v1(colon+1,UINT_MAX,&number);min=(unsigned)number;
            if(!error)error=ws_prep_unescape_v1(fields[4]);
            if(error||!ws_prep_path_v1(fields[4],1)||strlen(fields[4])>=sizeof(point)){error=ENOTSUP;break;}
            strcpy(point,fields[4]);
        }
        row=end+1;
    }
    free(bytes);if(error)return error;if(selected!=1)return ENOTSUP;
    if(capture){n->mount_id=id;strcpy(n->mountpoint,point);n->mount_device=(uint64_t)makedev(maj,min);}
    else if(n->mount_id!=id||strcmp(n->mountpoint,point)||n->mount_device!=(uint64_t)makedev(maj,min))return ESTALE;
    return 0;
}
/* Retain the path walk's descriptors; bounded depth avoids ephemeral FD cleanup
 * ambiguity. No symlink component or nested mount may replace the selected group. */
static int ws_contain_walk_v1(WsContainNativeV1* n,int root,const char* path,int group) {
    if(!ws_prep_path_v1(path,1)){errno=EINVAL;return -1;}
    int fd=root;const char* p=path+1;
    while(*p) {
        const char* end=strchr(p,'/');size_t size=end?(size_t)(end-p):strlen(p);
        if(size>255){errno=ENAMETOOLONG;return -1;}
        char name[256];memcpy(name,p,size);name[size]=0;
        if(n->link_count==64){errno=ENOSPC;return -1;}
        int parent=fd;
        fd=ws_contain_openat_v1(n,fd,name,O_RDONLY|O_DIRECTORY|O_NOFOLLOW);if(fd<0)return -1;
        int link=n->link_count++;n->link_parent[link]=parent;n->link_child[link]=fd;strcpy(n->link_name[link],name);
        if(group){uint64_t id;int e=ws_prep_mount_id_v1(fd,&id);if(e||id!=n->mount_id){errno=e?e:ESTALE;return -1;}}
        if(!end)break;p=end+1;
    }
    return fd;
}
static int ws_contain_group_v1(WsContainNativeV1* n,int capture) {
    /* Verify the retained ancestor chain, not just a still-linked old inode
     * after somebody replaced/renamed its original path. No path reopening. */
    for(int i=0;i<n->link_count;i++) {
        struct stat expected,actual;
        if(fstat(n->link_child[i],&expected)||fstatat(n->link_parent[i],n->link_name[i],&actual,AT_SYMLINK_NOFOLLOW))return errno;
        if(!S_ISDIR(actual.st_mode)||actual.st_dev!=expected.st_dev||actual.st_ino!=expected.st_ino||!actual.st_nlink)return ESTALE;
    }
    struct stat mount,group;struct statfs fs;uint64_t mid=0,gid=0;
    if(fstat(n->mountfd,&mount)||fstat(n->groupfd,&group)||fstatfs(n->groupfd,&fs))return errno;
    int e=ws_prep_mount_id_v1(n->mountfd,&mid);if(!e)e=ws_prep_mount_id_v1(n->groupfd,&gid);if(e)return e;
    if(fs.f_type!=CGROUP2_SUPER_MAGIC||mid!=n->mount_id||gid!=mid||!group.st_nlink||!mount.st_nlink||
       (uint64_t)mount.st_dev!=n->mount_device||group.st_dev!=mount.st_dev)return ESTALE;
    if((uint64_t)group.st_ino>INT64_MAX||(uint64_t)mount.st_ino>INT64_MAX||n->mount_device>INT64_MAX)return EOVERFLOW;
    if(capture){n->mount_inode=mount.st_ino;n->group_device=group.st_dev;n->group_inode=group.st_ino;}
    else if(n->mount_inode!=(uint64_t)mount.st_ino||n->group_inode!=(uint64_t)group.st_ino||n->group_device!=(uint64_t)group.st_dev)return ESTALE;
    return 0;
}
static int ws_contain_membership_v1(WsContainNativeV1* n,int fd) {
    char bytes[WS_CONTAIN_PROCS_V1+1];int error=ws_contain_read_v1(fd,bytes,sizeof(bytes));if(error)return error;
    int found=0;const char* p=bytes;
    while(*p){uint64_t value=0;error=ws_decimal_v1(&p,INT_MAX,&value);if(error||*p!='\n'||!value)return EINVAL;
        if(value==(uint64_t)n->pid)found++;p++;}
    return found==1?0:ESTALE;
}
static int ws_contain_start_v1(int fd,pid_t pid,uint64_t* ticks) {
    char bytes[8192];int error=ws_contain_read_v1(fd,bytes,sizeof(bytes));if(error)return error;
    const char* p=bytes;uint64_t observed=0;error=ws_decimal_v1(&p,INT_MAX,&observed);
    if(error||observed!=(uint64_t)pid||*p!=' ')return ESTALE;
    p=strrchr(p,')');if(!p||p[1]!=' '||!p[2]||p[3]!=' ')return EINVAL;p+=4;
    for(int field=4;field<22;field++) {
        const char* start=p;if(*p=='-')p++;
        while(*p>='0'&&*p<='9')p++;
        if(p==start||(p==start+1&&start[0]=='-')||*p!=' ')return EINVAL;p++;
    }
    error=ws_decimal_v1(&p,INT64_MAX,ticks);
    return error?error:(!*ticks||(*p!=' '&&*p!='\n')?EINVAL:0);
}
static int ws_contain_live_v1(WsContainNativeV1* n) {
    int error=ws_pidfd_live_v1(n->pidfd);if(error)return error;
    uint64_t ticks=0;char path[4096];
    error=ws_contain_start_v1(n->statfd,n->pid,&ticks);
    if(!error)error=ws_contain_read_v1(n->cgroupfd,path,sizeof(path));
    if(!error){char* end=strchr(path,'\n');if(strncmp(path,"0::",3)||!end||end[1])error=ENOTSUP;else{*end=0;memmove(path,path+3,strlen(path+3)+1);}}
    if(error)return error;if(strcmp(path,n->path)||(n->start_ticks&&ticks!=n->start_ticks))return ESTALE;
    n->start_ticks=ticks;return ws_pidfd_live_v1(n->pidfd);
}
static int ws_contain_open_v1(WsContainNativeV1* n,pid_t pid,const char* path) {
    n->pid=pid;if(!ws_cgroup_path_v1(path))return EINVAL;strcpy(n->path,path);
#ifdef SYS_pidfd_open
    n->pidfd=ws_contain_keep_v1(n,(int)syscall(SYS_pidfd_open,pid,0));
#else
    return ENOTSUP;
#endif
    if(n->pidfd<0)return errno;int error=ws_pidfd_live_v1(n->pidfd);if(error)return error;
    int proc=ws_contain_openat_v1(n,AT_FDCWD,"/proc",O_RDONLY|O_DIRECTORY|O_NOFOLLOW);if(proc<0)return errno;
    struct statfs fs;if(fstatfs(proc,&fs))return errno;if(fs.f_type!=PROC_SUPER_MAGIC)return ENOTSUP;
    char name[32];snprintf(name,sizeof(name),"%ld",(long)pid);
    n->procfd=ws_contain_openat_v1(n,proc,name,O_RDONLY|O_DIRECTORY|O_NOFOLLOW);
    n->observerfd=ws_contain_openat_v1(n,proc,"thread-self",O_RDONLY|O_DIRECTORY);
    if(n->procfd<0||n->observerfd<0)return errno;
    n->statfd=ws_contain_openat_v1(n,n->procfd,"stat",O_RDONLY|O_NOFOLLOW);
    n->cgroupfd=ws_contain_openat_v1(n,n->procfd,"cgroup",O_RDONLY|O_NOFOLLOW);
    int observer_stat=ws_contain_openat_v1(n,n->observerfd,"stat",O_RDONLY|O_NOFOLLOW);
    if(n->statfd<0||n->cgroupfd<0||observer_stat<0)return errno;
    uint64_t observer_ticks=0;
    error=ws_contain_start_v1(observer_stat,(pid_t)syscall(SYS_gettid),&observer_ticks);if(error)return error;
    error=ws_contain_live_v1(n);if(!error)error=ws_contain_namespaces_v1(n,1);if(error)return error;
    n->mountinfofd=ws_contain_openat_v1(n,n->observerfd,"mountinfo",O_RDONLY|O_NOFOLLOW);if(n->mountinfofd<0)return errno;
    error=ws_contain_mount_v1(n,1);if(error)return error;
    int root=ws_contain_openat_v1(n,AT_FDCWD,"/",O_RDONLY|O_DIRECTORY|O_NOFOLLOW);if(root<0)return errno;
    n->mountfd=ws_contain_walk_v1(n,root,n->mountpoint,0);if(n->mountfd<0)return errno;
    n->groupfd=ws_contain_walk_v1(n,n->mountfd,n->path,1);if(n->groupfd<0)return errno;
    error=ws_contain_group_v1(n,1);if(error)return error;
    int procs=ws_contain_openat_v1(n,n->groupfd,"cgroup.procs",O_RDONLY|O_NOFOLLOW);if(procs<0)return errno;
    n->eventsfd=ws_contain_openat_v1(n,n->groupfd,"cgroup.events",O_RDONLY|O_NOFOLLOW);if(n->eventsfd<0)return errno;
    error=ws_contain_membership_v1(n,procs);if(!error)error=ws_contain_live_v1(n);
    if(!error)error=ws_contain_namespaces_v1(n,2);
    if(!error)error=ws_contain_mount_v1(n,0);if(!error)error=ws_contain_group_v1(n,0);
    if(!error)n->captured=1;return error;
}
static int ws_contain_observe_v1(WsContainNativeV1* n,int* populated) {
    if(n->error||n->close_uncertain||!n->captured)return n->error?n->error:ESTALE;
    int error=ws_contain_namespaces_v1(n,0);if(!error)error=ws_contain_mount_v1(n,0);
    if(!error)error=ws_contain_group_v1(n,0);if(error)return error;
    char bytes[4097];error=ws_contain_read_v1(n->eventsfd,bytes,sizeof(bytes));
    if(!error&&!rt_lg_parse_populated(bytes,strlen(bytes),populated))error=EINVAL;
    if(!error)error=ws_contain_group_v1(n,0);if(!error)error=ws_contain_namespaces_v1(n,0);
    if(!error)error=ws_contain_mount_v1(n,0);
    return error;
}
static int ws_contain_close_v1(WsContainNativeV1* n) {
    if(n->close_uncertain)return n->close_uncertain;
    for(int i=n->count-1;i>=0;i--)if(n->fds[i]>=0) {
        int fd=n->fds[i];n->fds[i]=-1;
        if(close(fd)){n->close_uncertain=errno?errno:EIO;return n->close_uncertain;}
    }
    return 0;
}
#endif
