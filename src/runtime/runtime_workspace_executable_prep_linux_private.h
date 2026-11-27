/* Trusted keeper-stage executable preparation. Include after the workspace
 * storage and user-observation private headers. No registry or authorization
 * policy lives here: the common consumer must verify the exact keeper manifest
 * and retained authorization, and reobserve the storage/user owners itself.
 * This additional native check refuses unsupported mount/credential layouts.
 * Snapshot comparisons detect races; they are not a kernel filesystem seal. */
#ifndef SIMPLE_WORKSPACE_EXECUTABLE_PREP_LINUX_PRIVATE_H
#define SIMPLE_WORKSPACE_EXECUTABLE_PREP_LINUX_PRIVATE_H
#include <sys/statvfs.h>
#include <sys/sysmacros.h>

#define WS_PREP_MOUNT_BYTES_V1 (256u * 1024u)
#define WS_PREP_MOUNT_ROWS_V1 512u
#define WS_PREP_PATH_V1 4096u
#define WS_PREP_FILE_BYTES_V1 UINT64_C(1073741824)

typedef struct {
    int state; /* 0 refused, 1 prepared, 2 uncertain after attempted chmod */
    int error;
    char file_identity[192], digest[65];
    uint64_t size_bytes;
    uint32_t old_mode, new_mode;
} WsExecutablePrepFactsV1;
typedef struct {
    uint64_t id;
    unsigned major_id, minor_id;
    char *root, *point, *options, *source, *type;
} WsPrepMountRowV1;
typedef struct {
    char raw[WS_PREP_MOUNT_BYTES_V1 + 1];
    char parsed[WS_PREP_MOUNT_BYTES_V1 + 1];
    WsPrepMountRowV1 rows[WS_PREP_MOUNT_ROWS_V1];
    size_t count;
    uint64_t namespace_device, namespace_inode;
    int namespace_fd; /* initial namespace pin only; -1 for refresh snapshots */
} WsPrepMountsV1;

static int ws_prep_path_v1(const char* path,int absolute) {
    if(!path)return 0;
    size_t length=strnlen(path,WS_PREP_PATH_V1);
    if(!length||length==WS_PREP_PATH_V1||(absolute?(path[0]!='/'):(path[0]=='/')))return 0;
    if(absolute&&length==1)return 1;
    if(path[length-1]=='/')return 0;
    const char* p=path+(absolute?1:0);
    while(*p) {
        const char* end=strchr(p,'/');size_t n=end?(size_t)(end-p):strlen(p);
        if(!n||(n==1&&p[0]=='.')||(n==2&&p[0]=='.'&&p[1]=='.'))return 0;
        for(size_t i=0;i<n;i++)if((unsigned char)p[i]<32||(unsigned char)p[i]==127)return 0;
        if(!end)break;p=end+1;
    }
    return 1;
}
/* Some unrelated kernel mounts (notably nsfs) have opaque roots such as
 * mnt:[4026531840]. Preserve bounded metadata, but never use an opaque root
 * for selected filesystem scope or same-device alias reasoning. */
static int ws_prep_mount_root_v1(const char* root,int path_required) {
    if(!root)return 0;
    size_t length=strnlen(root,WS_PREP_PATH_V1);
    if(!length||length==WS_PREP_PATH_V1)return 0;
    for(size_t i=0;i<length;i++)if((unsigned char)root[i]<32||(unsigned char)root[i]==127)return 0;
    return path_required?ws_prep_path_v1(root,1):1;
}
static int ws_prep_under_v1(const char* path,const char* parent) {
    size_t n=strlen(parent);
    return !strcmp(parent,"/")||(!strncmp(path,parent,n)&&(path[n]==0||path[n]=='/'));
}
static int ws_prep_overlap_v1(const char* a,const char* b) {
    return ws_prep_under_v1(a,b)||ws_prep_under_v1(b,a);
}
static int ws_prep_unsigned_v1(const char* p,uint64_t maximum,uint64_t* out) {
    if(!p||!*p)return EINVAL;
    uint64_t value=0;
    for(;*p;p++) {
        if(*p<'0'||*p>'9')return EINVAL;
        unsigned digit=(unsigned)(*p-'0');
        if(value>(maximum-digit)/10)return EOVERFLOW;
        value=value*10+digit;
    }
    if(value>maximum)return EOVERFLOW;*out=value;return 0;
}
/* mountinfo escapes are kernel octal byte escapes, not shell quoting. */
static int ws_prep_unescape_v1(char* text) {
    char* output=text;
    for(char* p=text;*p;p++) {
        unsigned value=(unsigned char)*p;
        if(*p=='\\') {
            if(!p[1]||!p[2]||!p[3]||p[1]<'0'||p[1]>'7'||p[2]<'0'||p[2]>'7'||p[3]<'0'||p[3]>'7')return EINVAL;
            value=(unsigned)(p[1]-'0')*64+(unsigned)(p[2]-'0')*8+(unsigned)(p[3]-'0');p+=3;
            if(value>255)return EINVAL;
        }
        if(value<32||value==127)return ENOTSUP;
        *output++=(char)value;
    }
    *output=0;return 0;
}
static int ws_prep_option_v1(const char* options,const char* wanted) {
    size_t n=strlen(wanted);
    for(const char* p=options;*p;) {
        const char* end=strchr(p,',');size_t size=end?(size_t)(end-p):strlen(p);
        if(n==size&&!strncmp(p,wanted,n))return 1;
        if(!end)break;p=end+1;
    }
    return 0;
}
static int ws_prep_mount_read_v1(int proc,WsPrepMountsV1* mounts,int retain_namespace) {
    memset(mounts,0,sizeof(*mounts));mounts->namespace_fd=-1;
    int ns=openat(proc,"ns/mnt",O_RDONLY|O_CLOEXEC);if(ns<0)return errno;
    if(retain_namespace)mounts->namespace_fd=ns;
    struct stat st;int error=0;
    if(fstat(ns,&st))error=errno;
    else if(ioctl(ns,NS_GET_NSTYPE)!=CLONE_NEWNS)error=ENOTSUP;
    if(!retain_namespace)close(ns);if(error)return error;
    mounts->namespace_device=(uint64_t)st.st_dev;mounts->namespace_inode=(uint64_t)st.st_ino;
    error=ws_proc_read_v1(proc,"mountinfo",mounts->raw,sizeof(mounts->raw));if(error)return error;
    strcpy(mounts->parsed,mounts->raw);
    char* cursor=mounts->parsed;
    while(*cursor) {
        if(mounts->count==WS_PREP_MOUNT_ROWS_V1)return EOVERFLOW;
        char* end=strchr(cursor,'\n');if(!end)return EINVAL;*end=0;
        char* fields[128];size_t count=0;
        for(char* p=cursor;*p;) {
            if(count==128)return EOVERFLOW;fields[count++]=p;
            char* space=strchr(p,' ');if(!space)break;*space=0;p=space+1;if(!*p||*p==' ')return EINVAL;
        }
        if(count<10)return EINVAL;
        size_t separator=6;while(separator<count&&strcmp(fields[separator],"-"))separator++;
        if(separator+4!=count)return EINVAL;
        WsPrepMountRowV1* row=&mounts->rows[mounts->count];uint64_t number;
        if((error=ws_prep_unsigned_v1(fields[0],UINT64_MAX,&row->id))||!row->id)return error?error:EINVAL;
        for(size_t i=0;i<mounts->count;i++)if(mounts->rows[i].id==row->id)return EINVAL;
        if((error=ws_prep_unsigned_v1(fields[1],UINT64_MAX,&number)))return error;
        char* colon=strchr(fields[2],':');if(!colon)return EINVAL;*colon=0;
        if((error=ws_prep_unsigned_v1(fields[2],UINT_MAX,&number)))return error;row->major_id=(unsigned)number;
        if((error=ws_prep_unsigned_v1(colon+1,UINT_MAX,&number)))return error;row->minor_id=(unsigned)number;
        row->root=fields[3];row->point=fields[4];row->options=fields[5];row->type=fields[separator+1];row->source=fields[separator+2];
        if((error=ws_prep_unescape_v1(row->root))||(error=ws_prep_unescape_v1(row->point))||
                (error=ws_prep_unescape_v1(row->source)))return error;
        if(!ws_prep_mount_root_v1(row->root,0)||!ws_prep_path_v1(row->point,1))return ENOTSUP;
        if(ws_prep_option_v1(row->options,"ro")==ws_prep_option_v1(row->options,"rw"))return ENOTSUP;
        mounts->count++;cursor=end+1;
    }
    return mounts->count?0:ENOTSUP;
}
static int ws_prep_mount_id_v1(int fd,uint64_t* id) {
#if defined(SYS_statx) && defined(STATX_MNT_ID)
    struct statx value;memset(&value,0,sizeof(value));
    if(syscall(SYS_statx,fd,"",AT_EMPTY_PATH|AT_SYMLINK_NOFOLLOW,STATX_MNT_ID,&value))return errno;
    if(!(value.stx_mask&STATX_MNT_ID))return ENOTSUP;*id=value.stx_mnt_id;return 0;
#else
    (void)fd;(void)id;return ENOTSUP;
#endif
}
static WsPrepMountRowV1* ws_prep_mount_find_v1(WsPrepMountsV1* mounts,uint64_t id) {
    for(size_t i=0;i<mounts->count;i++)if(mounts->rows[i].id==id)return &mounts->rows[i];
    return NULL;
}
static int ws_prep_project_v1(int fd,WsNativeV1* storage,int directory) {
    struct stat st;struct statfs fs;struct fsxattr attr;memset(&attr,0,sizeof(attr));
    if(fstat(fd,&st)||fstatfs(fd,&fs))return errno;
    if((directory?!S_ISDIR(st.st_mode):!S_ISREG(st.st_mode))||
            (uint64_t)st.st_dev!=storage->device||fs.f_type!=XFS_SUPER_MAGIC||
            st.st_uid!=geteuid()||(st.st_mode&0022)||(directory&&!(st.st_mode&S_IXUSR)))return EPERM;
    if(ioctl(fd,FS_IOC_FSGETXATTR,&attr))return errno;
    if(attr.fsx_projid!=storage->project||(directory&&!(attr.fsx_xflags&FS_XFLAG_PROJINHERIT)))return ESTALE;
    return 0;
}
/* Access is evaluated using the target's verified equal effective/FS IDs.
 * Never credit supplemental groups, root/CAP_DAC_OVERRIDE or caller privileges. */
static int ws_prep_traverse_v1(int fd) {
    struct stat st;if(fstat(fd,&st))return errno;
    if(!S_ISDIR(st.st_mode))return ENOTDIR;
    mode_t bit=st.st_uid==geteuid()?S_IXUSR:st.st_gid==getegid()?S_IXGRP:S_IXOTH;
    return (st.st_mode&bit)?0:EACCES;
}
static int ws_prep_walk_v1(int root,const char* relative,int directory,WsNativeV1* storage,int host,int* out) {
    *out=-1;if(!ws_prep_path_v1(relative,0))return EINVAL;
    char path[WS_PREP_PATH_V1];strcpy(path,relative);
    int fd=fcntl(root,F_DUPFD_CLOEXEC,3);if(fd<0)return errno;
    int error=0;uint64_t root_mount=0;
    if(host&&(error=ws_prep_project_v1(fd,storage,1))){close(fd);return error;}
    if(!host&&(error=ws_prep_traverse_v1(fd))){close(fd);return error;}
    /* Fixed guest mount roots may cross mounts; executable descendants may not.
     * Host input/output roots and all descendants must stay on workspace mount. */
    int fixed_mount=host||!directory;
    if(fixed_mount&&(error=ws_prep_mount_id_v1(fd,&root_mount))){close(fd);return error;}
    for(char* p=path;*p;) {
        char* slash=strchr(p,'/');if(slash)*slash=0;
        int isdir=slash!=NULL||directory;
        /* O_NONBLOCK prevents a hostile replaced leaf FIFO from blocking. */
        int next=openat(fd,p,O_RDONLY|O_CLOEXEC|O_NOFOLLOW|O_NONBLOCK|(isdir?O_DIRECTORY:0));
        if(next<0){error=errno;close(fd);return error;}close(fd);fd=next;
        if(host&&(error=ws_prep_project_v1(fd,storage,isdir))){close(fd);return error;}
        if(!host&&isdir&&(error=ws_prep_traverse_v1(fd))){close(fd);return error;}
        if(fixed_mount) {
            uint64_t child_mount=0;error=ws_prep_mount_id_v1(fd,&child_mount);
            if(!error&&child_mount!=root_mount)error=EXDEV;
            if(error){close(fd);return error;}
        }
        if(!slash)break;p=slash+1;
    }
    *out=fd;return 0;
}
static int ws_prep_same_v1(int a,int b) {
    struct stat x,y;if(fstat(a,&x)||fstat(b,&y))return errno;
    return x.st_dev==y.st_dev&&x.st_ino==y.st_ino&&x.st_uid==y.st_uid?0:ESTALE;
}
static int ws_prep_same_mount_v1(int a,int b) {
    int error=ws_prep_same_v1(a,b);if(error)return error;
    uint64_t x,y;
    if((error=ws_prep_mount_id_v1(a,&x))||(error=ws_prep_mount_id_v1(b,&y)))return error;
    return x==y?0:ESTALE;
}
static int ws_prep_host_root_v1(WsUserNativeV1* user,int fd,WsPrepMountsV1* mounts,
        char root[WS_PREP_PATH_V1],WsPrepMountRowV1** row_out) {
    uint64_t id;int error=ws_prep_mount_id_v1(fd,&id);if(error)return error;
    WsPrepMountRowV1* row=ws_prep_mount_find_v1(mounts,id);if(!row)return ENOTSUP;
    if(!ws_prep_mount_root_v1(row->root,1))return ENOTSUP;
    char link[64],path[WS_PREP_PATH_V1];int n=snprintf(link,sizeof(link),"fd/%d",fd);
    if(n<0||(size_t)n>=sizeof(link))return EOVERFLOW;
    ssize_t length=readlinkat(user->observer_procfd,link,path,sizeof(path)-1);
    if(length<0)return errno;if((size_t)length>=sizeof(path)-1)return EOVERFLOW;path[length]=0;
    if(!ws_prep_path_v1(path,1)||!ws_prep_under_v1(path,row->point)||strstr(path," (deleted)"))return ESTALE;
    struct stat st;if(fstat(fd,&st))return errno;
    if(row->major_id!=major(st.st_dev)||row->minor_id!=minor(st.st_dev))return ESTALE;
    const char* suffix=path+strlen(row->point);if(!strcmp(row->point,"/"))suffix=path;
    if(!strcmp(row->root,"/"))n=snprintf(root,WS_PREP_PATH_V1,"%s",*suffix?suffix:"/");
    else n=snprintf(root,WS_PREP_PATH_V1,"%s%s",row->root,suffix);
    if(n<0||(size_t)n>=WS_PREP_PATH_V1||!ws_prep_path_v1(root,1))return ENOTSUP;
    *row_out=row;return 0;
}
static int ws_prep_alias_v1(WsUserNativeV1* user,int input,int output,int guest_input,int guest_output,
        WsPrepMountsV1* host,WsPrepMountsV1* target) {
    char input_root[WS_PREP_PATH_V1],output_root[WS_PREP_PATH_V1];WsPrepMountRowV1 *hi,*ho;
    int error=ws_prep_host_root_v1(user,input,host,input_root,&hi);if(error)return error;
    error=ws_prep_host_root_v1(user,output,host,output_root,&ho);if(error)return error;
    if(ws_prep_overlap_v1(input_root,output_root))return EPERM;
    uint64_t iid,oid;if((error=ws_prep_mount_id_v1(guest_input,&iid))||(error=ws_prep_mount_id_v1(guest_output,&oid)))return error;
    WsPrepMountRowV1* ti=ws_prep_mount_find_v1(target,iid);WsPrepMountRowV1* to=ws_prep_mount_find_v1(target,oid);
    if(!ti||!to||strcmp(ti->point,"/simple-build/inputs")||strcmp(to->point,"/simple-build/outputs")||
            strcmp(ti->root,input_root)||strcmp(to->root,output_root)||strcmp(ti->source,hi->source)||strcmp(to->source,ho->source)||
            strcmp(ti->type,hi->type)||strcmp(to->type,ho->type)||
            ti->major_id!=hi->major_id||ti->minor_id!=hi->minor_id||to->major_id!=ho->major_id||to->minor_id!=ho->minor_id||
            !ws_prep_option_v1(ti->options,"ro")||!ws_prep_option_v1(to->options,"rw"))return EPERM;
    for(size_t i=0;i<target->count;i++) {
        WsPrepMountRowV1* row=&target->rows[i];
        if(row->major_id==hi->major_id&&row->minor_id==hi->minor_id) {
            if(!ws_prep_mount_root_v1(row->root,1))return ENOTSUP;
            if(ws_prep_option_v1(row->options,"rw")&&ws_prep_overlap_v1(row->root,input_root))return EPERM;
        }
    }
    struct statvfs in,out;if(fstatvfs(guest_input,&in)||fstatvfs(guest_output,&out))return errno;
    struct stat output_stat;if(fstat(output,&output_stat))return errno;
    if((output_stat.st_mode&(S_IWUSR|S_IXUSR))!=(S_IWUSR|S_IXUSR))return EACCES;
    if(in.f_flag&ST_NOEXEC)return EACCES;
    return (in.f_flag&ST_RDONLY)&&!(out.f_flag&ST_RDONLY)?0:EROFS;
}
/* Reopen path membership through retained roots, never through readlink text.
 * Identity checks bind both names to the same pinned objects at this instant. */
static int ws_prep_membership_v1(WsNativeV1* storage,WsUserNativeV1* user,
        const char* input_path,const char* output_path,const char* file_path,
        int input,int output,int file,int target_root,int guest_input,int guest_output,int guest_file) {
    int fd=-1,error=0;
    error=ws_prep_walk_v1(storage->workspace_fd,input_path,1,storage,1,&fd);
    if(!error)error=ws_prep_same_mount_v1(input,fd);if(fd>=0)close(fd);fd=-1;if(error)return error;
    error=ws_prep_walk_v1(storage->workspace_fd,output_path,1,storage,1,&fd);
    if(!error)error=ws_prep_same_mount_v1(output,fd);if(fd>=0)close(fd);fd=-1;if(error)return error;
    error=ws_prep_walk_v1(input,file_path,0,storage,1,&fd);
    if(!error)error=ws_prep_same_mount_v1(file,fd);if(fd>=0)close(fd);fd=-1;if(error)return error;
    fd=openat(user->procfd,"root",O_RDONLY|O_DIRECTORY|O_CLOEXEC);if(fd<0)return errno;
    error=ws_prep_same_mount_v1(target_root,fd);close(fd);fd=-1;if(error)return error;
    error=ws_prep_walk_v1(target_root,"simple-build/inputs",1,storage,0,&fd);
    if(!error)error=ws_prep_same_mount_v1(guest_input,fd);if(fd>=0)close(fd);fd=-1;if(error)return error;
    error=ws_prep_walk_v1(target_root,"simple-build/outputs",1,storage,0,&fd);
    if(!error)error=ws_prep_same_mount_v1(guest_output,fd);if(fd>=0)close(fd);fd=-1;if(error)return error;
    error=ws_prep_walk_v1(guest_input,file_path,0,storage,0,&fd);
    if(!error)error=ws_prep_same_mount_v1(guest_file,fd);if(fd>=0)close(fd);return error;
}
static int ws_prep_file_equal_v1(const struct stat* a,const struct stat* b) {
    return a->st_dev==b->st_dev&&a->st_ino==b->st_ino&&a->st_uid==b->st_uid&&a->st_gid==b->st_gid&&
        a->st_nlink==b->st_nlink&&a->st_size==b->st_size&&a->st_mode==b->st_mode&&
        a->st_mtim.tv_sec==b->st_mtim.tv_sec&&a->st_mtim.tv_nsec==b->st_mtim.tv_nsec&&
        a->st_ctim.tv_sec==b->st_ctim.tv_sec&&a->st_ctim.tv_nsec==b->st_ctim.tv_nsec;
}
static int ws_prep_deadline_v1(int64_t monotonic_ms,int64_t unix_ms,int wall) {
    if(monotonic_ms<=0||unix_ms<=0)return EINVAL;
    struct timespec now;
    if(clock_gettime(CLOCK_MONOTONIC,&now))return errno;
    if(now.tv_sec<0||(uint64_t)now.tv_sec>((uint64_t)INT64_MAX-999)/1000)return EOVERFLOW;
    int64_t milliseconds=(int64_t)now.tv_sec*1000+now.tv_nsec/1000000;
    if(milliseconds>=monotonic_ms)return ETIMEDOUT;
    if(wall) {
        if(clock_gettime(CLOCK_REALTIME,&now))return errno;
        if(now.tv_sec<0||(uint64_t)now.tv_sec>((uint64_t)INT64_MAX-999)/1000)return EOVERFLOW;
        milliseconds=(int64_t)now.tv_sec*1000+now.tv_nsec/1000000;
        if(milliseconds>=unix_ms)return ETIMEDOUT;
    }
    return 0;
}
/* Streaming adapter only: compression and round constants belong exclusively to
 * the existing owned SHA owner. Never mmap an attacker-truncatable file. */
static int ws_prep_hash_v1(int fd,char output[65],struct stat* snapshot,int64_t deadline_ms,int64_t expires_ms) {
    struct stat before,after;if(fstat(fd,&before))return errno;
    if(!S_ISREG(before.st_mode)||before.st_size<0||(uint64_t)before.st_size>WS_PREP_FILE_BYTES_V1)return EFBIG;
    uint32_t state[8]={0x6a09e667u,0xbb67ae85u,0x3c6ef372u,0xa54ff53au,0x510e527fu,0x9b05688cu,0x1f83d9abu,0x5be0cd19u};
    uint8_t block[64],chunk[65536];uint64_t offset=0,total=(uint64_t)before.st_size;size_t pending=0;
    while(offset<total) {
        int error=ws_prep_deadline_v1(deadline_ms,expires_ms,0);if(error)return error;
        size_t want=sizeof(chunk);if((uint64_t)want>total-offset)want=(size_t)(total-offset);
        ssize_t got=pread(fd,chunk,want,(off_t)offset);
        if(got<0){if(errno==EINTR)continue;return errno;}if(!got)return ESTALE;
        size_t consumed=0;
        while(consumed<(size_t)got) {
            size_t take=64-pending;if(take>(size_t)got-consumed)take=(size_t)got-consumed;
            memcpy(block+pending,chunk+consumed,take);pending+=take;consumed+=take;
            if(pending==64){owned_sha256_block(state,block);pending=0;}
        }
        offset+=(uint64_t)got;
    }
    int deadline_error=ws_prep_deadline_v1(deadline_ms,expires_ms,0);if(deadline_error)return deadline_error;
    uint8_t extra;ssize_t end=pread(fd,&extra,1,(off_t)total);if(end<0)return errno;if(end)return ESTALE;
    block[pending++]=0x80;
    if(pending>56){memset(block+pending,0,64-pending);owned_sha256_block(state,block);pending=0;}
    memset(block+pending,0,56-pending);uint64_t bits=total*8;
    for(unsigned i=0;i<8;i++)block[63-i]=(uint8_t)(bits>>(8*i));owned_sha256_block(state,block);
    static const char hex[]="0123456789abcdef";
    for(unsigned i=0;i<32;i++){uint8_t byte=(uint8_t)(state[i/4]>>(24-8*(i%4)));output[i*2]=hex[byte>>4];output[i*2+1]=hex[byte&15];}output[64]=0;
    if(fstat(fd,&after))return errno;if(!ws_prep_file_equal_v1(&before,&after))return ESTALE;
    *snapshot=after;return 0;
}
static int ws_prep_user_v1(WsUserNativeV1* user) {
    WsUserFactsV1 observed;int error=ws_user_snapshot_v1(user,user->facts.cgroup,&observed);if(error)return error;
    if(memcmp(&observed,&user->facts,sizeof(observed)))return ESTALE;
    if(observed.effective_uid!=(uint32_t)geteuid()||observed.filesystem_uid!=(uint32_t)geteuid()||
            observed.effective_gid!=(uint32_t)getegid()||observed.filesystem_gid!=(uint32_t)getegid())return EPERM;
    return 0;
}

static int ws_prepare_executable_v1(WsNativeV1* storage,WsUserNativeV1* user,
        const char* input_relative_root,const char* output_relative_root,
        const char* executable_relative_path,const char* expected_sha256,
        int64_t deadline_monotonic_ms,int64_t expires_at_unix_ms,WsExecutablePrepFactsV1* result) {
    if(!result)return EINVAL;memset(result,0,sizeof(*result));
    int error=EINVAL,attempted=0;
    int input=-1,output=-1,file=-1,target_root=-1,guest_input=-1,guest_output=-1,guest_file=-1;
    WsPrepMountsV1 *host=NULL,*target=NULL,*again=NULL;
    if(!storage||!user||storage->workspace_fd<0||storage->parent_fd<0||!storage->project||
            !input_relative_root||!output_relative_root||!executable_relative_path||!expected_sha256)goto done;
    if(strcmp(executable_relative_path,"producer.exe")&&strcmp(executable_relative_path,"tools/simple"))goto done;
    if(strnlen(expected_sha256,65)!=64)goto done;
    for(size_t i=0;i<64;i++)if(!((expected_sha256[i]>='0'&&expected_sha256[i]<='9')||(expected_sha256[i]>='a'&&expected_sha256[i]<='f')))goto done;
    if(!ws_prep_path_v1(input_relative_root,0)||!ws_prep_path_v1(output_relative_root,0)||
            ws_prep_overlap_v1(input_relative_root,output_relative_root))goto done;
    if((error=ws_prep_deadline_v1(deadline_monotonic_ms,expires_at_unix_ms,1))||
            (error=ws_prep_user_v1(user)))goto done;
    struct stat workspace;if(fstat(storage->workspace_fd,&workspace)){error=errno;goto done;}
    if((uint64_t)workspace.st_dev!=storage->device||(uint64_t)workspace.st_ino!=storage->inode){error=ESTALE;goto done;}
    if((error=ws_prep_walk_v1(storage->workspace_fd,input_relative_root,1,storage,1,&input))||
            (error=ws_prep_walk_v1(storage->workspace_fd,output_relative_root,1,storage,1,&output))||
            (error=ws_prep_walk_v1(input,executable_relative_path,0,storage,1,&file)))goto done;
    target_root=openat(user->procfd,"root",O_RDONLY|O_DIRECTORY|O_CLOEXEC);if(target_root<0){error=errno;goto done;}
    if((error=ws_prep_walk_v1(target_root,"simple-build/inputs",1,storage,0,&guest_input))||
            (error=ws_prep_walk_v1(target_root,"simple-build/outputs",1,storage,0,&guest_output))||
            (error=ws_prep_walk_v1(guest_input,executable_relative_path,0,storage,0,&guest_file))||
            (error=ws_prep_same_v1(input,guest_input))||(error=ws_prep_same_v1(output,guest_output))||
            (error=ws_prep_same_v1(file,guest_file)))goto done;
    host=calloc(1,sizeof(*host));target=calloc(1,sizeof(*target));again=calloc(1,sizeof(*again));
    if(host)host->namespace_fd=-1;if(target)target->namespace_fd=-1;if(again)again->namespace_fd=-1;
    if(!host||!target||!again){error=ENOMEM;goto done;}
    if((error=ws_prep_mount_read_v1(user->observer_procfd,host,1))||(error=ws_prep_mount_read_v1(user->procfd,target,1))||
            (error=ws_prep_alias_v1(user,input,output,guest_input,guest_output,host,target)))goto done;
    struct stat before,after;int file_generation=0;
    if(ioctl(file,FS_IOC_GETVERSION,&file_generation)){error=errno;goto done;}
    if((error=ws_prep_hash_v1(file,result->digest,&before,deadline_monotonic_ms,expires_at_unix_ms)))goto done;
    result->size_bytes=(uint64_t)before.st_size;result->old_mode=(uint32_t)(before.st_mode&07777);
    result->new_mode=result->old_mode|S_IXUSR;
    int identity=snprintf(result->file_identity,sizeof(result->file_identity),"inode:%llu:%llu:%u:%llu",
            (unsigned long long)before.st_dev,(unsigned long long)before.st_ino,(unsigned)file_generation,(unsigned long long)before.st_uid);
    if(identity<0||(size_t)identity>=sizeof(result->file_identity)){error=EOVERFLOW;goto done;}
    if(before.st_nlink!=1||before.st_uid!=geteuid()||(before.st_mode&(S_ISUID|S_ISGID|S_ISVTX|0022))||
            strcmp(result->digest,expected_sha256)){error=EPERM;goto done;}
    struct statvfs guest_fs;if(fstatvfs(guest_file,&guest_fs)){error=errno;goto done;}
    if(!(guest_fs.f_flag&ST_RDONLY)){error=EROFS;goto done;}
    if(guest_fs.f_flag&ST_NOEXEC){error=EACCES;goto done;}
    if((error=ws_prep_user_v1(user)))goto done;
    if((error=ws_prep_mount_read_v1(user->observer_procfd,again,0)))goto done;
    if(strcmp(host->raw,again->raw)||host->namespace_device!=again->namespace_device||host->namespace_inode!=again->namespace_inode){error=ESTALE;goto done;}
    if((error=ws_prep_mount_read_v1(user->procfd,again,0)))goto done;
    if(strcmp(target->raw,again->raw)||target->namespace_device!=again->namespace_device||target->namespace_inode!=again->namespace_inode){error=ESTALE;goto done;}
    if((error=ws_prep_alias_v1(user,input,output,guest_input,guest_output,host,target))||
            (error=ws_prep_membership_v1(storage,user,input_relative_root,output_relative_root,executable_relative_path,
                input,output,file,target_root,guest_input,guest_output,guest_file)))goto done;
    struct stat immediate;if(fstat(file,&immediate)){error=errno;goto done;}
    if(!ws_prep_file_equal_v1(&before,&immediate)){error=ESTALE;goto done;}
    if((error=ws_prep_project_v1(file,storage,0))||(error=ws_prep_user_v1(user))||
            (error=ws_prep_deadline_v1(deadline_monotonic_ms,expires_at_unix_ms,1)))goto done;
    attempted=1;result->state=2;
    if(fchmod(file,(mode_t)result->new_mode)){error=errno;goto done;}
    /* Everything below is post-effect validation. A failure retains uncertain
     * facts and never tries to undo permission changes or delete an object. */
    if((error=ws_prep_hash_v1(file,result->digest,&after,deadline_monotonic_ms,expires_at_unix_ms)))goto done;
    if(strcmp(result->digest,expected_sha256)||after.st_dev!=before.st_dev||after.st_ino!=before.st_ino||
            after.st_uid!=before.st_uid||after.st_gid!=before.st_gid||after.st_nlink!=1||after.st_size!=before.st_size||
            (uint32_t)(after.st_mode&07777)!=result->new_mode||after.st_mtim.tv_sec!=before.st_mtim.tv_sec||
            after.st_mtim.tv_nsec!=before.st_mtim.tv_nsec){error=ESTALE;goto done;}
    if((error=ws_prep_mount_read_v1(user->observer_procfd,again,0)))goto done;
    if(strcmp(host->raw,again->raw)||host->namespace_device!=again->namespace_device||host->namespace_inode!=again->namespace_inode){error=ESTALE;goto done;}
    if((error=ws_prep_mount_read_v1(user->procfd,again,0)))goto done;
    if(strcmp(target->raw,again->raw)||target->namespace_device!=again->namespace_device||target->namespace_inode!=again->namespace_inode){error=ESTALE;goto done;}
    if((error=ws_prep_alias_v1(user,input,output,guest_input,guest_output,host,target)))goto done;
    if((error=ws_prep_membership_v1(storage,user,input_relative_root,output_relative_root,executable_relative_path,
            input,output,file,target_root,guest_input,guest_output,guest_file)))goto done;
    if(fstatvfs(guest_file,&guest_fs)){error=errno;goto done;}
    if(!(guest_fs.f_flag&ST_RDONLY)||(guest_fs.f_flag&ST_NOEXEC)){error=ESTALE;goto done;}
    int final_generation=0;if(ioctl(file,FS_IOC_GETVERSION,&final_generation)){error=errno;goto done;}
    if(final_generation!=file_generation){error=ESTALE;goto done;}
    if((error=ws_prep_project_v1(file,storage,0))||(error=ws_prep_user_v1(user)))goto done;
    if((error=ws_prep_deadline_v1(deadline_monotonic_ms,expires_at_unix_ms,1)))goto done;
    result->state=1;error=0;
done:
    {
        int descriptors[]={input,output,file,target_root,guest_input,guest_output,guest_file};
        for(size_t i=0;i<sizeof(descriptors)/sizeof(descriptors[0]);i++)
            if(descriptors[i]>=0&&close(descriptors[i])&& !error)error=errno?errno:EIO;
    }
    if(host&&host->namespace_fd>=0&&close(host->namespace_fd)&&!error)error=errno?errno:EIO;
    if(target&&target->namespace_fd>=0&&close(target->namespace_fd)&&!error)error=errno?errno:EIO;
    free(host);free(target);free(again);
    result->error=error;if(error)result->state=attempted?2:0;
    return error;
}
#endif
