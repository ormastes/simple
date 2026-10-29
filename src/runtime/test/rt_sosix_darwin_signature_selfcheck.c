#include "../runtime_sosix_darwin_signature_private.h"
#include <assert.h>
#include <fcntl.h>
#include <stdio.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

static void reject_authenticated(unsigned char *bytes,size_t length) {
    unsigned char digest[32],cdhash[20],*output=NULL;size_t output_length=0;
    CC_SHA256(bytes,(CC_LONG)length,digest);
    assert(sosix_darwin_provision_macho(bytes,length,digest,&output,&output_length,cdhash)!=0);
    assert(!output && !output_length);
}
static void malformed_matrix(const unsigned char *source,size_t length) {
    unsigned char *copy=malloc(length);assert(copy);
    struct mach_header_64 header;memcpy(&header,source,sizeof(header));
    size_t cursor=sizeof(header),signature=0,linkedit=0,loader=0,other=0;
    for(uint32_t i=0;i<header.ncmds;i++) {
        struct load_command command;memcpy(&command,source+cursor,sizeof(command));
        if(command.cmd==LC_CODE_SIGNATURE)signature=cursor;
        if(command.cmd==LC_LOAD_DYLINKER)loader=cursor;
        if(command.cmd==LC_UUID)other=cursor;
        if(command.cmd==LC_SEGMENT_64) {
            struct segment_command_64 segment;memcpy(&segment,source+cursor,sizeof(segment));
            if(!strncmp(segment.segname,"__LINKEDIT",16))linkedit=cursor;
        }
        cursor+=command.cmdsize;
    }
    assert(signature && linkedit && loader && other);
    for(int test=0;test<9;test++) {
        memcpy(copy,source,length);
        struct mach_header_64 altered=header;uint32_t value=0;
        if(test==0){altered.ncmds=UINT32_MAX;memcpy(copy,&altered,sizeof(altered));}
        if(test==1){altered.sizeofcmds=UINT32_MAX;memcpy(copy,&altered,sizeof(altered));}
        if(test==2)memcpy(copy+sizeof(header)+4,&value,4);
        if(test==3){value=UINT32_MAX;memcpy(copy+signature+8,&value,4);}
        if(test==4)memcpy(copy+signature+12,&value,4);
        if(test==5 || test==6) {
            size_t at=test==5?signature:linkedit;
            struct load_command duplicate;memcpy(&duplicate,source+at,sizeof(duplicate));
            assert(cursor+duplicate.cmdsize<=length);
            memcpy(copy+cursor,source+at,duplicate.cmdsize);
            altered.ncmds++;altered.sizeofcmds+=duplicate.cmdsize;memcpy(copy,&altered,sizeof(altered));
        }
        if(test==7){struct dylinker_command dl;memcpy(&dl,source+loader,sizeof(dl));copy[loader+dl.name.offset]='X';}
        if(test==8){value=LC_DYLD_ENVIRONMENT;memcpy(copy+other,&value,4);}
        reject_authenticated(copy,length);
    }
    free(copy);
    puts("PASS: authenticated malformed load commands signatures and loader policies reject");
}

int main(int argc,char **argv) {
    assert(argc==3);
    int input=open(argv[1],O_RDONLY); assert(input>=0);
    struct stat st; assert(!fstat(input,&st) && st.st_size>0);
    unsigned char *source=malloc((size_t)st.st_size); assert(source);
    assert(read(input,source,(size_t)st.st_size)==st.st_size); close(input);
    malformed_matrix(source,(size_t)st.st_size);
    unsigned char digest[32],cdhash[20],*signed_bytes=NULL; size_t signed_length=0;
    CC_SHA256(source,(CC_LONG)st.st_size,digest);
    unsigned char bad_digest[32];memcpy(bad_digest,digest,32);bad_digest[0]^=1;
    assert(sosix_darwin_provision_macho(source,(size_t)st.st_size,bad_digest,&signed_bytes,&signed_length,cdhash)==ESTALE);
    assert(!signed_bytes && !signed_length);
    source[0]^=1;
    assert(sosix_darwin_provision_macho(source,(size_t)st.st_size,digest,&signed_bytes,&signed_length,cdhash)==ESTALE);
    CC_SHA256(source,(CC_LONG)st.st_size,bad_digest);
    assert(sosix_darwin_provision_macho(source,(size_t)st.st_size,bad_digest,&signed_bytes,&signed_length,cdhash)==ENOTSUP);
    source[0]^=1;
    assert(sosix_darwin_provision_macho(source,3,digest,&signed_bytes,&signed_length,cdhash)==ENOEXEC);
    int result=sosix_darwin_provision_macho(source,(size_t)st.st_size,digest,&signed_bytes,&signed_length,cdhash);
    if (result) fprintf(stderr,"provision result=%d\n",result);
    assert(result==0 && signed_bytes && signed_length>0);
    int output=open(argv[2],O_WRONLY|O_CREAT|O_EXCL,0700); assert(output>=0);
    assert(write(output,signed_bytes,signed_length)==(ssize_t)signed_length); close(output);
    free(signed_bytes); free(source);
    posix_spawnattr_t attributes; assert(!posix_spawnattr_init(&attributes));
    unsigned char requirement[82]; assert(!sosix_darwin_amfi_attach(&attributes,cdhash,requirement));
    char *arguments[]={argv[2],"plain","",NULL},*environment[]={NULL}; pid_t pid=-1;
    assert(!posix_spawn(&pid,argv[2],NULL,&attributes,arguments,environment));
    posix_spawnattr_destroy(&attributes); int status; assert(waitpid(pid,&status,0)==pid);
    if(!WIFEXITED(status)||WEXITSTATUS(status))fprintf(stderr,"signed child status=%d\n",status);
    assert(WIFEXITED(status)&&WEXITSTATUS(status)==0);
    puts("PASS: authenticated in-memory signature provisions an executable accepted by AMFI");
}
