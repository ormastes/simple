/* Actual running-kernel/context observation only. Neither approved source
 * manifests nor terminal containment are attested by these native facts. */
#ifndef SIMPLE_WORKSPACE_KERNEL_OBSERVATION_LINUX_PRIVATE_H
#define SIMPLE_WORKSPACE_KERNEL_OBSERVATION_LINUX_PRIVATE_H
#include <stddef.h>
#include <sys/prctl.h>
#include <sys/utsname.h>
#define WS_KERNEL_NOTES_BYTES_V1 65536u

typedef struct {
    pid_t pid,tid;
    int seccomp,status_seccomp,tracer,dumpable,nnp,status_nnp;
    uint64_t proc_device,proc_inode,sysfs_device,sysfs_inode,notes_device,notes_inode;
    char release[257],build_id[129],notes_digest[65];
} WsKernelFactsV1;

static int ws_kernel_hex_v1(const char* value) {
    size_t n=strlen(value);if(n<2||n>128||(n%2))return 0;
    for(size_t i=0;i<n;i++)if(!((value[i]>='0'&&value[i]<='9')||(value[i]>='a'&&value[i]<='f')))return 0;
    return 1;
}
static int ws_kernel_release_v1(const char* value) {
    size_t n=strlen(value);if(!n||n>256)return 0;
    for(size_t i=0;i<n;i++)if((unsigned char)value[i]<32||(unsigned char)value[i]>126||value[i]=='/')return 0;
    return 1;
}
/* Linux's built-in .notes use the running target's byte order; no ELF file
 * headers or external tools are involved. Bounds precede every alignment/add. */
static int ws_kernel_notes_parse_v1(const uint8_t* bytes,size_t length,char build_id[129]) {
    size_t offset=0,records=0;int found=0;build_id[0]=0;
    while(offset<length) {
        if(++records>256||length-offset<12)return EINVAL;
        uint32_t namesz,descsz,type;
        memcpy(&namesz,bytes+offset,4);memcpy(&descsz,bytes+offset+4,4);memcpy(&type,bytes+offset+8,4);offset+=12;
        if(namesz>WS_KERNEL_NOTES_BYTES_V1||descsz>WS_KERNEL_NOTES_BYTES_V1)return EOVERFLOW;
        size_t name_bytes=((size_t)namesz+3)&~(size_t)3;
        size_t desc_bytes=((size_t)descsz+3)&~(size_t)3;
        if(name_bytes>length-offset||desc_bytes>length-offset-name_bytes)return EINVAL;
        if(type==3&&namesz==4&&!memcmp(bytes+offset,"GNU\0",4)) {
            if(found++||descsz<1||descsz>64)return EINVAL;
            static const char hex[]="0123456789abcdef";
            for(size_t i=0;i<descsz;i++){unsigned v=bytes[offset+name_bytes+i];build_id[i*2]=hex[v>>4];build_id[i*2+1]=hex[v&15];}
            build_id[(size_t)descsz*2]=0;
        }
        offset+=name_bytes+desc_bytes;
    }
    return found==1?0:ENOTSUP;
}
static int ws_kernel_binary_read_v1(int fd,uint8_t* bytes,size_t capacity,size_t* length) {
    size_t used=0;
    while(used<capacity) {
        ssize_t got=pread(fd,bytes+used,capacity-used,(off_t)used);
        if(got<0)return errno;if(!got)break;used+=(size_t)got;
    }
    if(used==capacity){uint8_t extra;ssize_t got=pread(fd,&extra,1,(off_t)used);if(got)return got<0?errno:EOVERFLOW;}
    if(!used)return EINVAL;*length=used;return 0;
}
static int ws_kernel_status_v1(const char* bytes,WsKernelFactsV1* f) {
    const char* names[]={"Tgid:","Pid:","TracerPid:","Seccomp:","NoNewPrivs:"};
    uint64_t values[5]={0};unsigned seen=0;
    for(const char* row=bytes;*row;) {
        const char* end=strchr(row,'\n');if(!end)return EINVAL;
        for(size_t i=0;i<5;i++)if(!strncmp(row,names[i],strlen(names[i]))) {
            if(seen&(1u<<i))return EINVAL;seen|=1u<<i;
            const char* cursor=row+strlen(names[i]);int error=ws_decimal_v1(&cursor,INT_MAX,&values[i]);
            if(error||cursor!=end)return EINVAL;
        }
        row=end+1;
    }
    if(seen!=31||values[0]!=(uint64_t)getpid()||values[1]!=(uint64_t)syscall(SYS_gettid))return ESTALE;
    f->pid=(pid_t)values[0];f->tid=(pid_t)values[1];f->tracer=(int)values[2];
    f->status_seccomp=(int)values[3];f->status_nnp=(int)values[4];return 0;
}
static int ws_kernel_context_v1(WsContainNativeV1* n,WsKernelFactsV1* f) {
    if(n->kernel_tid!=(pid_t)syscall(SYS_gettid))return EXDEV;
    int error=ws_contain_namespaces_v1(n,0);if(error)return error;
    int seccomp=prctl(PR_GET_SECCOMP,0,0,0,0),dumpable=prctl(PR_GET_DUMPABLE,0,0,0,0);
    int nnp=prctl(PR_GET_NO_NEW_PRIVS,0,0,0,0);
    if(seccomp<0||dumpable<0||nnp<0)return errno?errno:EIO;
    if(seccomp!=0||dumpable!=0||(nnp!=0&&nnp!=1))return EPERM;
    char bytes[65537];error=ws_contain_read_v1(n->kernel_statusfd,bytes,sizeof(bytes));if(error)return error;
    error=ws_kernel_status_v1(bytes,f);if(error)return error;
    if(f->tracer||f->status_seccomp!=seccomp||f->status_nnp!=nnp)return EPERM;
    if(prctl(PR_GET_SECCOMP,0,0,0,0)!=seccomp||prctl(PR_GET_DUMPABLE,0,0,0,0)!=dumpable||
       prctl(PR_GET_NO_NEW_PRIVS,0,0,0,0)!=nnp)return ESTALE;
    f->seccomp=seccomp;f->dumpable=dumpable;f->nnp=nnp;
    return ws_contain_namespaces_v1(n,0);
}
static int ws_kernel_objects_v1(WsContainNativeV1* n,WsKernelFactsV1* f) {
    struct stat proc,sysfs,dir,notes,current;struct statfs fs;uint64_t root_mount,dir_mount,note_mount;
    if(fstat(n->observerfd,&proc)||fstatfs(n->observerfd,&fs))return errno;
    if(fs.f_type!=PROC_SUPER_MAGIC)return ENOTSUP;
    if(fstat(n->kernel_sysfsfd,&sysfs)||fstat(n->kernel_dirfd,&dir)||fstat(n->kernel_notesfd,&notes)||fstatfs(n->kernel_notesfd,&fs))return errno;
    if(fs.f_type!=SYSFS_MAGIC||sysfs.st_dev!=dir.st_dev||notes.st_dev!=dir.st_dev||!S_ISREG(notes.st_mode))return ENOTSUP;
    if(fstatat(n->kernel_rootfd,"sys",&current,AT_SYMLINK_NOFOLLOW)||current.st_dev!=sysfs.st_dev||current.st_ino!=sysfs.st_ino)return ESTALE;
    if(fstatat(n->kernel_sysfsfd,"kernel",&current,AT_SYMLINK_NOFOLLOW)||current.st_dev!=dir.st_dev||current.st_ino!=dir.st_ino)return ESTALE;
    if(fstatat(n->kernel_dirfd,"notes",&current,AT_SYMLINK_NOFOLLOW)||current.st_dev!=notes.st_dev||current.st_ino!=notes.st_ino)return ESTALE;
    int error=ws_prep_mount_id_v1(n->kernel_sysfsfd,&root_mount);
    if(!error)error=ws_prep_mount_id_v1(n->kernel_dirfd,&dir_mount);if(!error)error=ws_prep_mount_id_v1(n->kernel_notesfd,&note_mount);
    if(error)return error;if(root_mount!=dir_mount||root_mount!=note_mount)return ESTALE;
    if((uint64_t)proc.st_dev>INT64_MAX||(uint64_t)proc.st_ino>INT64_MAX||(uint64_t)sysfs.st_dev>INT64_MAX||
       (uint64_t)sysfs.st_ino>INT64_MAX||(uint64_t)notes.st_dev>INT64_MAX||(uint64_t)notes.st_ino>INT64_MAX)return EOVERFLOW;
    f->proc_device=proc.st_dev;f->proc_inode=proc.st_ino;f->sysfs_device=sysfs.st_dev;f->sysfs_inode=sysfs.st_ino;
    f->notes_device=notes.st_dev;f->notes_inode=notes.st_ino;return 0;
}
static int ws_kernel_open_once_v1(WsContainNativeV1* n) {
    /* Reuse partial descriptors. Never overwrite an unresolved owner on retry. */
    pid_t tid=(pid_t)syscall(SYS_gettid);
    if(n->kernel_tid&&n->kernel_tid!=tid)return EXDEV;
    if(prctl(PR_GET_SECCOMP,0,0,0,0)!=0||prctl(PR_GET_DUMPABLE,0,0,0,0)!=0)return EPERM;
    if(n->kernel_statusfd<0)n->kernel_statusfd=ws_contain_openat_v1(n,n->observerfd,"status",O_RDONLY|O_NOFOLLOW);
    if(n->kernel_statusfd<0)return errno;
    char status[65537];WsKernelFactsV1 f;memset(&f,0,sizeof(f));
    int error=ws_contain_read_v1(n->kernel_statusfd,status,sizeof(status));if(error)return error;
    error=ws_kernel_status_v1(status,&f);if(error)return error;n->kernel_tid=tid;
    /* Refuse hostile syscall context before notes-path acquisition. */
    error=ws_kernel_context_v1(n,&f);if(error)return error;
    if(n->kernel_rootfd<0)n->kernel_rootfd=ws_contain_openat_v1(n,AT_FDCWD,"/",O_RDONLY|O_DIRECTORY|O_NOFOLLOW);
    if(n->kernel_rootfd<0)return errno;
    if(n->kernel_sysfsfd<0)n->kernel_sysfsfd=ws_contain_openat_v1(n,n->kernel_rootfd,"sys",O_RDONLY|O_DIRECTORY|O_NOFOLLOW);
    if(n->kernel_sysfsfd<0)return errno;
    if(n->kernel_dirfd<0)n->kernel_dirfd=ws_contain_openat_v1(n,n->kernel_sysfsfd,"kernel",O_RDONLY|O_DIRECTORY|O_NOFOLLOW);
    if(n->kernel_dirfd<0)return errno;
    if(n->kernel_notesfd<0)n->kernel_notesfd=ws_contain_openat_v1(n,n->kernel_dirfd,"notes",O_RDONLY|O_NOFOLLOW);
    return n->kernel_notesfd<0?errno:0;
}
static int ws_kernel_observe_v1(WsContainNativeV1* n,const char* release,const char* build,WsKernelFactsV1* facts) {
    if(!n->captured||n->error||n->close_uncertain)return ESTALE;
    if(!ws_kernel_release_v1(release)||!ws_kernel_hex_v1(build))return EINVAL;
    int error=ws_kernel_open_once_v1(n);if(error)return error;
    WsKernelFactsV1 before,after;memset(&before,0,sizeof(before));memset(&after,0,sizeof(after));
    error=ws_kernel_context_v1(n,&before);if(!error)error=ws_kernel_objects_v1(n,&before);if(error)return error;
    uint8_t notes[WS_KERNEL_NOTES_BYTES_V1];size_t length=0;struct utsname actual;
    if(uname(&actual))return errno;
    if(strnlen(actual.release,sizeof(actual.release))==sizeof(actual.release)||strcmp(actual.release,release))return ESTALE;
    error=ws_kernel_binary_read_v1(n->kernel_notesfd,notes,sizeof(notes),&length);if(error)return error;
    error=ws_kernel_notes_parse_v1(notes,length,before.build_id);if(error)return error;
    if(strcmp(before.build_id,build))return ESTALE;
    uint8_t hash[32];owned_sha256(notes,length,hash);static const char hex[]="0123456789abcdef";
    for(size_t i=0;i<32;i++){before.notes_digest[i*2]=hex[hash[i]>>4];before.notes_digest[i*2+1]=hex[hash[i]&15];}
    strcpy(before.release,actual.release);
    error=ws_kernel_context_v1(n,&after);if(!error)error=ws_kernel_objects_v1(n,&after);if(error)return error;
    /* Compare only actual context/native identities, before textual facts. */
    if(memcmp(&before,&after,offsetof(WsKernelFactsV1,release)))return ESTALE;
    struct utsname final;if(uname(&final)||strcmp(actual.release,final.release))return ESTALE;
    *facts=before;return 0;
}
#endif
