static void before_spawn_attack(void *image);
#define SOSIX_DARWIN_IMAGE_BEFORE_SPAWN(image) before_spawn_attack(image)
#include "../runtime_sosix_darwin_process_private.h"
#include <assert.h>
#include <mach-o/dyld.h>

static int attack_mode,retained=-1;
static off_t mutation_offset;
static char replacement[PATH_MAX];
static const char signed_payload[]="SOSIX_BOUND_PAYLOAD_8b7bd8ea";
static void mark_environment(const char *key) {
    const char *path=getenv(key);if(!path)return;
    int fd=open(path,O_WRONLY|O_CREAT|O_EXCL,0600);if(fd>=0){assert(write(fd,"1",1)==1);close(fd);}
}
__attribute__((constructor))static void mark_constructor(void){mark_environment("BOUND_CONSTRUCTOR_MARKER");}

static void before_spawn_attack(void *raw) {
    SosixDarwinImage *image=raw;
    if(attack_mode==1)assert(!rename(replacement,image->path));
    if(attack_mode==2)assert(pwrite(retained,"X",1,mutation_offset)==1);
}

static void copy_fd(int source,const char *path) {
    int output=open(path,O_WRONLY|O_CREAT|O_EXCL,0700);assert(output>=0);
    unsigned char bytes[65536];off_t offset=0;
    for(;;){ssize_t n=pread(source,bytes,sizeof(bytes),offset);assert(n>=0);if(!n)break;
        assert(write(output,bytes,(size_t)n)==n);offset+=n;}
    assert(!close(output));
}

static int run_owner(int source,const unsigned char digest[32],int mode,char *const env[]) {
    SosixDarwinImage image;assert(!sosix_darwin_image_create_bound(source,digest,&image));
    assert(image.kernel_bound && !memcmp(image.source_digest,digest,32));
    char constructor_path[PATH_MAX],main_path[PATH_MAX],constructor_env[PATH_MAX+64],main_env[PATH_MAX+64];
    snprintf(constructor_path,sizeof(constructor_path),"%s/constructor",image.directory);
    snprintf(main_path,sizeof(main_path),"%s/main",image.directory);
    snprintf(constructor_env,sizeof(constructor_env),"BOUND_CONSTRUCTOR_MARKER=%s",constructor_path);
    snprintf(main_env,sizeof(main_env),"BOUND_MAIN_MARKER=%s",main_path);
    char *marked_env[16];size_t env_count=0;
    while(env[env_count]){assert(env_count<12);marked_env[env_count]=env[env_count];env_count++;}
    marked_env[env_count++]=constructor_env;marked_env[env_count++]=main_env;marked_env[env_count]=NULL;
    if(mode==1){snprintf(replacement,sizeof(replacement),"%s/replacement",image.directory);copy_fd(source,replacement);}
    if(mode==2) {
        assert(!chmod(image.path,0700));retained=open(image.path,O_RDWR);assert(retained>=0);
        struct stat st;assert(!fstat(retained,&st));unsigned char *bytes=malloc((size_t)st.st_size);assert(bytes);
        assert(pread(retained,bytes,(size_t)st.st_size,0)==st.st_size);mutation_offset=-1;
        for(off_t i=0;i+(off_t)sizeof(signed_payload)<=st.st_size;i++)
            if(!memcmp(bytes+i,signed_payload,sizeof(signed_payload))){mutation_offset=i;break;}
        free(bytes);assert(mutation_offset>=0);
    }
    int cwd=open("/private/tmp",O_RDONLY|O_DIRECTORY|O_CLOEXEC);assert(cwd>=0);
    SosixDarwinProcess owner;SosixDarwinProcessLimits limits={1000000000LL,10000000LL,1000000000LL,4096,4096};
    char *args[]={"bound-child","--child",NULL};attack_mode=mode;
    assert(!sosix_darwin_process_start(&owner,&image,image.generation,cwd,args,marked_env,limits));
    attack_mode=0;close(cwd);if(retained>=0){close(retained);retained=-1;}
    while(!owner.frozen)assert(!sosix_darwin_process_poll(&owner,owner.generation,10000000LL));
    assert(owner.reaped && owner.group_retired && !owner.cleanup_error);
    int status=owner.wait_status;
    if(!mode || mode==3){assert(WIFEXITED(status)&&WEXITSTATUS(status)==0);assert(owner.stdout_kept==5&&!memcmp(owner.stdout_bytes,"BOUND",5));}
    else {assert(owner.stdout_kept==0);assert(WIFSIGNALED(status));}
    if(mode==1){assert(access(constructor_path,F_OK)<0&&errno==ENOENT);assert(access(main_path,F_OK)<0&&errno==ENOENT);}
    if(!mode || mode==3){assert(!access(constructor_path,F_OK));assert(!access(main_path,F_OK));}
    if(access(constructor_path,F_OK)==0)assert(!unlink(constructor_path));
    if(access(main_path,F_OK)==0)assert(!unlink(main_path));
    assert(!sosix_darwin_process_ack(&owner,owner.generation));
    assert(!sosix_darwin_image_close(&image,image.generation));return status;
}

int main(int argc,char **argv) {
    if(argc>1 && !strcmp(argv[1],"--child")) {
        mark_environment("BOUND_MAIN_MARKER");
        const volatile char *payload=signed_payload;if(payload[0]!='S')return 99;
        const char *library=getenv("BOUND_TEST_DYLIB");
        if(library && dlopen(library,RTLD_NOW|RTLD_LOCAL))return 97;
        return write(STDOUT_FILENO,"BOUND",5)==5?0:98;
    }
    assert(argc==3);
    char path[PATH_MAX];uint32_t capacity=sizeof(path);assert(!_NSGetExecutablePath(path,&capacity));
    int source=open(path,O_RDONLY|O_CLOEXEC);assert(source>=0);
    unsigned char digest[32];assert(!sosix_darwin_image_hash(source,digest));
    SosixDarwinImage denied;unsigned char wrong[32];memcpy(wrong,digest,32);wrong[0]^=1;
    assert(sosix_darwin_image_create_bound(source,wrong,&denied)==ESTALE);assert(!denied.generation&&denied.fd==-1);
    puts("PASS: wrong authenticated digest is rejected before image ownership");
    SosixDarwinImage grown;assert(!sosix_darwin_image_create_bound(source,digest,&grown));
    assert(!chmod(grown.path,0700));int growth=open(grown.path,O_WRONLY);assert(growth>=0);
    assert(!ftruncate(growth,INT64_C(1)<<40));close(growth);
    pid_t rejected_pid=-1;char *rejected_args[]={"child","--child",NULL},*no_environment[]={NULL};
    int64_t began=sosix_darwin_process_now();
    assert(sosix_darwin_image_spawn(&grown,grown.generation,&rejected_pid,NULL,NULL,rejected_args,no_environment)==ESTALE);
    assert(sosix_darwin_process_now()-began<1000000000LL && rejected_pid==-1);
    assert(!sosix_darwin_image_close(&grown,grown.generation));
    puts("PASS: attacker sparse-file growth is rejected without unbounded rehash or spawn");
    char *clean_env[]={NULL};run_owner(source,digest,0,clean_env);
    puts("PASS: authenticated source provisions and executes through the real process owner");
    int replaced_status=run_owner(source,digest,1,clean_env);assert(WTERMSIG(replaced_status)==SIGKILL);
    puts("PASS: post-validation replacement is killed before executable constructor and main entry");
    int mutated_status=run_owner(source,digest,2,clean_env);assert(WTERMSIG(mutated_status)==SIGKILL);
    puts("PASS: retained-FD mutation terminates without a successful child result");
    char injection[PATH_MAX+64],marker[PATH_MAX+64],direct[PATH_MAX+64];
    snprintf(injection,sizeof(injection),"DYLD_INSERT_LIBRARIES=%s",argv[1]);
    snprintf(marker,sizeof(marker),"SOSIX_LIBRARY_MARKER=%s",argv[2]);char *injected_env[]={injection,marker,NULL,NULL};
    pid_t positive=-1;char *args[]={path,"--child",NULL};
    posix_spawn_file_actions_t quiet;assert(!posix_spawn_file_actions_init(&quiet));
    assert(!posix_spawn_file_actions_addopen(&quiet,STDOUT_FILENO,"/dev/null",O_WRONLY,0));
    assert(!posix_spawn(&positive,path,&quiet,NULL,args,injected_env));posix_spawn_file_actions_destroy(&quiet);
    int status;assert(waitpid(positive,&status,0)==positive);
    assert(WIFEXITED(status)&&!WEXITSTATUS(status)&&!access(argv[2],F_OK));assert(!unlink(argv[2]));
    puts("PASS: unconstrained source proves injected library can execute");
    snprintf(direct,sizeof(direct),"BOUND_TEST_DYLIB=%s",argv[1]);injected_env[2]=direct;
    run_owner(source,digest,3,injected_env);assert(access(argv[2],F_OK)<0&&errno==ENOENT);
    puts("PASS: provisioned owner denies direct and injected custom dependencies before constructors");
    close(source);
}
