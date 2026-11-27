/* Narrow native Mach-O provisioning from authenticated in-memory bytes.
 * Private AMFI LWCR v1 encoding; no filesystem signing or signing identity.
 * This profile removes entitlements and admits system libraries only.
 */
#ifndef RUNTIME_SOSIX_DARWIN_SIGNATURE_PRIVATE_H
#define RUNTIME_SOSIX_DARWIN_SIGNATURE_PRIVATE_H
#ifdef __APPLE__
#include <CommonCrypto/CommonDigest.h>
#include <mach-o/loader.h>
#include <mach/machine.h>
#include <sys/sysctl.h>
#include <dlfcn.h>
#include <spawn.h>
#include <errno.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#define SOSIX_DARWIN_BOUND_MAX_BYTES (256U * 1024U * 1024U)
#define SOSIX_DARWIN_LWCR_BYTES 82

/* Exact DER emitted by Apple's LWCR serializer for version 1, category 0,
 * requirements {cdhash: <20 bytes>}. A native parity test checks this encoding
 * against libTLE. The kernel consumes the bytes before posix_spawn returns. */
static void sosix_darwin_cdhash_requirement(const unsigned char hash[20], unsigned char out[82]) {
    static const unsigned char format[82] = {
        0x70,0x50,0x02,0x01,0x01,0xb0,0x4b,0x30,0x09,0x0c,0x04,0x63,0x63,0x61,0x74,0x02,0x01,0x00,
        0x30,0x09,0x0c,0x04,0x63,0x6f,0x6d,0x70,0x02,0x01,0x01,0x30,0x28,0x0c,0x04,0x72,0x65,0x71,
        0x73,0xb0,0x20,0x30,0x1e,0x0c,0x06,0x63,0x64,0x68,0x61,0x73,0x68,0x04,0x14,
        0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
        0x30,0x09,0x0c,0x04,0x76,0x65,0x72,0x73,0x02,0x01,0x01
    };
    memcpy(out,format,sizeof(format)); memcpy(out+51,hash,20);
}

static int sosix_darwin_amfi_attach(posix_spawnattr_t *attributes, const unsigned char cdhash[20], unsigned char storage[82]) {
    if (!attributes || !cdhash || !storage) return EINVAL;
    int allowed=0; size_t size=sizeof(allowed);
    if (sysctlbyname("security.mac.amfi.launch_constraints_3rd_party_allowed",&allowed,&size,NULL,0) ||
        size != sizeof(allowed) || allowed != 1) return ENOTSUP;
    int (*attach)(posix_spawnattr_t *,const char *,void *,size_t) =
        (int (*)(posix_spawnattr_t *,const char *,void *,size_t))dlsym(RTLD_DEFAULT,"posix_spawnattr_setmacpolicyinfo_np");
    if (!attach) return ENOTSUP;
    sosix_darwin_cdhash_requirement(cdhash,storage);
    return attach(attributes,"AMFI",storage,82);
}

static void sosix_darwin_put_be32(unsigned char *out,uint32_t value) {
    out[0]=(unsigned char)(value>>24); out[1]=(unsigned char)(value>>16);
    out[2]=(unsigned char)(value>>8); out[3]=(unsigned char)value;
}
static void sosix_darwin_put_be64(unsigned char *out,uint64_t value) {
    sosix_darwin_put_be32(out,(uint32_t)(value>>32)); sosix_darwin_put_be32(out+4,(uint32_t)value);
}

/* Capture the input digest before interpreting any identity metadata. The new
 * ad-hoc signature is constructed from that same memory. No pathname lookup
 * can substitute a second executable during SHA256 -> CDHash derivation.
 * Only thin, native, dynamically linked standalone executables are admitted.
 * Existing signature metadata (including every entitlement) is discarded. */
static int sosix_darwin_provision_macho(const unsigned char *source,size_t length,
        const unsigned char expected_sha256[32],unsigned char **output,size_t *output_length,
        unsigned char cdhash[20]) {
    if (!source || !expected_sha256 || !output || !output_length || !cdhash) return EINVAL;
    *output=NULL; *output_length=0;
    if(length<sizeof(struct mach_header_64))return ENOEXEC;
    if(length>SOSIX_DARWIN_BOUND_MAX_BYTES)return EFBIG;
    unsigned char observed[32]; CC_SHA256(source,(CC_LONG)length,observed);
    unsigned difference=0; for(size_t i=0;i<32;i++)difference|=observed[i]^expected_sha256[i];
    if(difference)return ESTALE;
    struct mach_header_64 header; memcpy(&header,source,sizeof(header));
    if(header.magic!=MH_MAGIC_64 || header.filetype!=MH_EXECUTE || !(header.flags&MH_DYLDLINK))return ENOTSUP;
#if defined(__arm64__) || defined(__aarch64__)
    if(header.cputype!=CPU_TYPE_ARM64 || header.cpusubtype!=CPU_SUBTYPE_ARM64_ALL)return ENOTSUP;
#elif defined(__x86_64__)
    if(header.cputype!=CPU_TYPE_X86_64 || header.cpusubtype!=CPU_SUBTYPE_X86_64_ALL)return ENOTSUP;
#else
    return ENOTSUP;
#endif
    if(!header.ncmds || header.ncmds>4096 || header.sizeofcmds>1024*1024 ||
       header.sizeofcmds>length-sizeof(header))return ENOEXEC;
    size_t cursor=sizeof(header),end=cursor+header.sizeofcmds;
    size_t signature_command=0,linkedit_command=0; int dyld=0,entry=0;uint64_t entry_offset=0;
    struct linkedit_data_command signature={0}; struct segment_command_64 linkedit={0},text={0};
    for(uint32_t i=0;i<header.ncmds;i++) {
        struct load_command command;
        if(end-cursor<sizeof(command))return ENOEXEC;
        memcpy(&command,source+cursor,sizeof(command));
        if(command.cmdsize<sizeof(command) || command.cmdsize%8 || command.cmdsize>end-cursor)return ENOEXEC;
        if(command.cmd==LC_CODE_SIGNATURE) {
            if(signature_command || command.cmdsize!=sizeof(signature))return ENOEXEC;
            signature_command=cursor; memcpy(&signature,source+cursor,sizeof(signature));
        } else if(command.cmd==LC_SEGMENT_64) {
            struct segment_command_64 segment;
            if(command.cmdsize<sizeof(segment))return ENOEXEC;
            memcpy(&segment,source+cursor,sizeof(segment));
            if(segment.fileoff>length || segment.filesize>length-segment.fileoff ||
               segment.nsects>(command.cmdsize-sizeof(segment))/sizeof(struct section_64))return ENOEXEC;
            if(!strncmp(segment.segname,"__LINKEDIT",16)) {
                if(linkedit_command || segment.nsects || command.cmdsize!=sizeof(segment))return ENOEXEC;
                linkedit_command=cursor; linkedit=segment;
            } else if(!strncmp(segment.segname,"__TEXT",16)) {
                if(text.filesize || segment.fileoff || !segment.filesize)return ENOEXEC;
                text=segment;
            }
        } else if(command.cmd==LC_LOAD_DYLINKER) {
            struct dylinker_command loader;
            if(dyld++ || command.cmdsize<sizeof(loader))return ENOEXEC;
            memcpy(&loader,source+cursor,sizeof(loader));
            if(loader.name.offset<sizeof(loader) || loader.name.offset>=command.cmdsize ||
               !memchr(source+cursor+loader.name.offset,0,command.cmdsize-loader.name.offset) ||
               strcmp((const char*)source+cursor+loader.name.offset,"/usr/lib/dyld"))return ENOTSUP;
        } else if(command.cmd==LC_MAIN) {
            if(entry++ || command.cmdsize!=sizeof(struct entry_point_command))return ENOEXEC;
            struct entry_point_command main_command;memcpy(&main_command,source+cursor,sizeof(main_command));
            entry_offset=main_command.entryoff;
        } else if(command.cmd==LC_UNIXTHREAD || command.cmd==LC_DYLD_ENVIRONMENT ||
                  command.cmd==LC_ENCRYPTION_INFO || command.cmd==LC_ENCRYPTION_INFO_64) return ENOTSUP;
        cursor+=command.cmdsize;
    }
    if(cursor!=end || !signature_command || !linkedit_command || !text.filesize || dyld!=1 || entry!=1 ||
       signature.dataoff<end || signature.dataoff>length || signature.datasize!=length-signature.dataoff ||
       linkedit.fileoff>signature.dataoff || linkedit.filesize!=length-linkedit.fileoff ||
       text.filesize>signature.dataoff || entry_offset>=text.filesize)return ENOEXEC;
    /* No non-LINKEDIT segment may overlap bytes being replaced by signing. */
    cursor=sizeof(header);
    for(uint32_t i=0;i<header.ncmds;i++) {
        struct load_command command; memcpy(&command,source+cursor,sizeof(command));
        if(command.cmd==LC_SEGMENT_64 && cursor!=linkedit_command) {
            struct segment_command_64 segment; memcpy(&segment,source+cursor,sizeof(segment));
            if(segment.fileoff>signature.dataoff || segment.filesize>signature.dataoff-segment.fileoff)return ENOEXEC;
        }
        cursor+=command.cmdsize;
    }
    const char identifier[]="org.simple.sosix.bound-v1";
    size_t slots=((size_t)signature.dataoff+4095)/4096;
    size_t hash_offset=96+sizeof(identifier)+11*32;
    size_t directory_length=hash_offset+slots*32;
    size_t library_length=8+SOSIX_DARWIN_LWCR_BYTES;
    size_t blob_length=28+directory_length+library_length;
    size_t signature_length=(blob_length+15)&~(size_t)15;
    size_t total=(size_t)signature.dataoff+signature_length;
    if(total>SOSIX_DARWIN_BOUND_MAX_BYTES || signature_length>UINT32_MAX)return EFBIG;
    unsigned char *bytes=calloc(1,total); if(!bytes)return ENOMEM;
    memcpy(bytes,source,signature.dataoff);
    signature.datasize=(uint32_t)signature_length;
    memcpy(bytes+signature_command,&signature,sizeof(signature));
    linkedit.filesize=total-linkedit.fileoff;
#if defined(__arm64__) || defined(__aarch64__)
    linkedit.vmsize=(linkedit.filesize+16383)&~UINT64_C(16383);
#else
    linkedit.vmsize=(linkedit.filesize+4095)&~UINT64_C(4095);
#endif
    memcpy(bytes+linkedit_command,&linkedit,sizeof(linkedit));
    unsigned char *blob=bytes+signature.dataoff,*directory=blob+28,*library=directory+directory_length;
    sosix_darwin_put_be32(blob,0xfade0cc0); sosix_darwin_put_be32(blob+4,(uint32_t)blob_length);
    sosix_darwin_put_be32(blob+8,2); sosix_darwin_put_be32(blob+12,0); sosix_darwin_put_be32(blob+16,28);
    sosix_darwin_put_be32(blob+20,11); sosix_darwin_put_be32(blob+24,(uint32_t)(28+directory_length));
    sosix_darwin_put_be32(directory,0xfade0c02); sosix_darwin_put_be32(directory+4,(uint32_t)directory_length);
    sosix_darwin_put_be32(directory+8,0x20500); sosix_darwin_put_be32(directory+12,0x10302); /* ADHOC | HARD | KILL | RUNTIME */
    sosix_darwin_put_be32(directory+16,(uint32_t)hash_offset); sosix_darwin_put_be32(directory+20,96);
    sosix_darwin_put_be32(directory+24,11); sosix_darwin_put_be32(directory+28,(uint32_t)slots);
    sosix_darwin_put_be32(directory+32,signature.dataoff);
    directory[36]=32; directory[37]=2; directory[39]=12; /* SHA256, 4096-byte pages */
    sosix_darwin_put_be64(directory+64,text.fileoff); sosix_darwin_put_be64(directory+72,text.filesize);
    sosix_darwin_put_be64(directory+80,1); /* CS_EXECSEG_MAIN_BINARY */
    sosix_darwin_put_be32(directory+88,0x000d0000); /* Hardened runtime version 13.0.0, no exception entitlements. */
    memcpy(directory+96,identifier,sizeof(identifier));
    sosix_darwin_put_be32(library,0xfade8181); sosix_darwin_put_be32(library+4,(uint32_t)library_length);
    unsigned char impossible_hash[20]={0}; sosix_darwin_cdhash_requirement(impossible_hash,library+8);
    CC_SHA256(library,(CC_LONG)library_length,directory+hash_offset-11*32);
    for(size_t i=0;i<slots;i++) {
        size_t available=(size_t)signature.dataoff-i*4096; if(available>4096)available=4096;
        CC_SHA256(bytes+i*4096,(CC_LONG)available,directory+hash_offset+i*32);
    }
    CC_SHA256(directory,(CC_LONG)directory_length,observed); memcpy(cdhash,observed,20);
    *output=bytes; *output_length=total; return 0;
}
#endif
#endif
