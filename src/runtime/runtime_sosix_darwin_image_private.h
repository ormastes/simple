/* Darwin executable ownership. create() retains the cooperative snapshot
 * contract: same-UID path mutation can race its launch. create_bound() instead
 * authenticates source bytes and binds the provisioned CDHash in AMFI. Bound
 * files remain mutable; tampering must cause denial rather than other code.
 * Neither mode provides descendant containment. */
#ifndef RUNTIME_SOSIX_DARWIN_IMAGE_PRIVATE_H
#define RUNTIME_SOSIX_DARWIN_IMAGE_PRIVATE_H
#ifdef __APPLE__
#include <CommonCrypto/CommonDigest.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <spawn.h>
#include <unistd.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <errno.h>
#include <limits.h>
#include "runtime_sosix_darwin_signature_private.h"
#ifndef SOSIX_DARWIN_IMAGE_BEFORE_SPAWN
#define SOSIX_DARWIN_IMAGE_BEFORE_SPAWN(image) ((void)(image))
#endif

typedef struct {
    uint64_t generation;
    int fd;
    char directory[PATH_MAX];
    char path[PATH_MAX];
    unsigned char digest[CC_SHA256_DIGEST_LENGTH];
    dev_t device;
    ino_t inode;
    int kernel_bound;
    unsigned char source_digest[CC_SHA256_DIGEST_LENGTH];
    unsigned char cdhash[20];
    size_t provisioned_length;
    unsigned char amfi_requirement[82];
} SosixDarwinImage;

static int sosix_darwin_image_hash(int fd, unsigned char digest[CC_SHA256_DIGEST_LENGTH]) {
    CC_SHA256_CTX ctx; unsigned char buffer[65536]; off_t offset = 0;
    CC_SHA256_Init(&ctx);
    for (;;) {
        ssize_t n = pread(fd, buffer, sizeof(buffer), offset);
        if (n < 0 && errno == EINTR) continue;
        if (n < 0) return errno;
        if (!n) break;
        CC_SHA256_Update(&ctx, buffer, (CC_LONG)n); offset += n;
    }
    CC_SHA256_Final(digest, &ctx); return 0;
}

static int sosix_darwin_image_create(int source_fd, SosixDarwinImage *image) {
    if (!image) return EINVAL;
    memset(image, 0, sizeof(*image)); image->fd = -1;
    struct stat source;
    if (fstat(source_fd, &source) || !S_ISREG(source.st_mode) || source.st_size <= 0)
        return errno ? errno : EINVAL;
    const char *base = getenv("TMPDIR"); if (!base || !*base) base = "/tmp";
    /* Spawn actions may change cwd before the kernel resolves the image path.
     * Keep the snapshot path absolute even when the caller uses TMPDIR=.. */
    char absolute_base[PATH_MAX];
    if (!realpath(base, absolute_base)) return errno;
    if (snprintf(image->directory, sizeof(image->directory), "%s/sosix-image-XXXXXXXX", absolute_base) >= (int)sizeof(image->directory)) return ENAMETOOLONG;
    if (!mkdtemp(image->directory)) return errno;
    if (snprintf(image->path, sizeof(image->path), "%s/image", image->directory) >= (int)sizeof(image->path)) { rmdir(image->directory); return ENAMETOOLONG; }
    int write_fd = open(image->path, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC | O_NOFOLLOW, 0600);
    if (write_fd < 0) { int e = errno; rmdir(image->directory); return e; }
    int error = 0; unsigned char buffer[65536]; off_t offset = 0;
    while (offset < source.st_size) {
        size_t want = (size_t)(source.st_size - offset); if (want > sizeof(buffer)) want = sizeof(buffer);
        ssize_t n = pread(source_fd, buffer, want, offset);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) { error = n < 0 ? errno : EIO; break; }
        ssize_t done = 0;
        while (done < n) {
            ssize_t w = write(write_fd, buffer + done, (size_t)(n - done));
            if (w < 0 && errno == EINTR) continue;
            if (w <= 0) { error = w < 0 ? errno : EIO; break; }
            done += w;
        }
        if (error) break;
        offset += n;
    }
    if (!error && fchmod(write_fd, 0500)) error = errno;
    if (close(write_fd) && !error) error = errno;
    if (!error) { image->fd = open(image->path, O_RDONLY | O_CLOEXEC | O_NOFOLLOW); if (image->fd < 0) error = errno; }
    struct stat st;
    if (!error && (fstat(image->fd, &st) || !S_ISREG(st.st_mode))) error = errno ? errno : EIO;
    if (!error) { image->device = st.st_dev; image->inode = st.st_ino; error = sosix_darwin_image_hash(image->fd, image->digest); }
    if (error) { if (image->fd >= 0) close(image->fd); unlink(image->path); rmdir(image->directory); memset(image, 0, sizeof(*image)); image->fd = -1; return error; }
    do arc4random_buf(&image->generation, sizeof(image->generation)); while (!image->generation);
    return 0;
}

/* Authenticate a bounded snapshot before provisioning. Both content identity
 * and the derived kernel identity originate in the same captured memory. */
static int sosix_darwin_image_create_bound(int source_fd, const unsigned char expected_sha256[32], SosixDarwinImage *image) {
    if(!image || !expected_sha256)return EINVAL;
    memset(image,0,sizeof(*image)); image->fd=-1;
    struct stat source;
    if(fstat(source_fd,&source))return errno;
    if(!S_ISREG(source.st_mode) || source.st_size<=0)return EINVAL;
    if((uint64_t)source.st_size>SOSIX_DARWIN_BOUND_MAX_BYTES)return EFBIG;
    size_t length=(size_t)source.st_size,offset=0;
    unsigned char *captured=malloc(length),*provisioned=NULL; size_t provisioned_length=0;
    if(!captured)return ENOMEM;
    int error=0;
    while(offset<length) {
        ssize_t count=pread(source_fd,captured+offset,length-offset,(off_t)offset);
        if(count<0 && errno==EINTR)continue;
        if(count<=0){error=count<0?errno:EIO;break;}
        offset+=(size_t)count;
    }
    if(!error)error=sosix_darwin_provision_macho(captured,length,expected_sha256,
        &provisioned,&provisioned_length,image->cdhash);
    free(captured);
    if(error)return error;
    const char *base=getenv("TMPDIR"); if(!base || !*base)base="/tmp";
    char physical[PATH_MAX];
    if(!realpath(base,physical)) {error=errno;goto done;}
    if(snprintf(image->directory,sizeof(image->directory),"%s/sosix-bound-XXXXXXXX",physical)>=(int)sizeof(image->directory)) {error=ENAMETOOLONG;goto done;}
    if(!mkdtemp(image->directory)){error=errno;image->directory[0]=0;goto done;}
    if(snprintf(image->path,sizeof(image->path),"%s/image",image->directory)>=(int)sizeof(image->path)) {error=ENAMETOOLONG;goto done;}
    int writer=open(image->path,O_WRONLY|O_CREAT|O_EXCL|O_CLOEXEC|O_NOFOLLOW,0600);
    if(writer<0){error=errno;goto done;}
    offset=0;
    while(offset<provisioned_length) {
        ssize_t count=write(writer,provisioned+offset,provisioned_length-offset);
        if(count<0 && errno==EINTR)continue;
        if(count<=0){error=count<0?errno:EIO;break;}
        offset+=(size_t)count;
    }
    if(!error && fchmod(writer,0500))error=errno;
    if(close(writer) && !error)error=errno;
    if(!error) {image->fd=open(image->path,O_RDONLY|O_CLOEXEC|O_NOFOLLOW|O_NONBLOCK);if(image->fd<0)error=errno;}
    struct stat snapshot;
    if(!error && fstat(image->fd,&snapshot))error=errno;
    if(!error && (!S_ISREG(snapshot.st_mode) || snapshot.st_size!=(off_t)provisioned_length))error=ESTALE;
    if(!error) {
        image->device=snapshot.st_dev;image->inode=snapshot.st_ino;
        CC_SHA256(provisioned,(CC_LONG)provisioned_length,image->digest);
        memcpy(image->source_digest,expected_sha256,32);image->kernel_bound=1;
        image->provisioned_length=provisioned_length;
        do arc4random_buf(&image->generation,sizeof(image->generation)); while(!image->generation);
    }
done:
    free(provisioned);
    if(error) {
        if(image->fd>=0)close(image->fd);
        if(image->path[0])unlink(image->path);
        if(image->directory[0])rmdir(image->directory);
        memset(image,0,sizeof(*image));image->fd=-1;
    }
    return error;
}

/* Bound-mode attributes borrow policy bytes from image. Destroy the attributes
 * before closing that image; never reuse them after image ownership ends. */
static int sosix_darwin_image_spawn(SosixDarwinImage *image, uint64_t generation, pid_t *pid,
        const posix_spawn_file_actions_t *actions, posix_spawnattr_t *attributes,
        char *const argv[], char *const environment[]) {
    if (!image || !generation || image->generation != generation || image->fd < 0) return ESTALE;
    if (!pid || !argv || !environment) return EINVAL;
    struct stat st; unsigned char digest[CC_SHA256_DIGEST_LENGTH];
    if (lstat(image->path, &st)) return errno;
    if (!S_ISREG(st.st_mode) || st.st_dev != image->device || st.st_ino != image->inode) return ESTALE;
    int error=0;
    if(image->kernel_bound) {
        if(st.st_size<0 || (uint64_t)st.st_size!=image->provisioned_length)return ESTALE;
        /* Never hash attacker-mutable bytes until a moving EOF. AMFI, not a
         * userspace rehash, authorizes this image. In-place changes can fault
         * later during paging; no modified signed page may be admitted. */
    } else {
        error=sosix_darwin_image_hash(image->fd,digest);
        if(error)return error;
        if(memcmp(digest,image->digest,sizeof(digest)))return ESTALE;
    }
    posix_spawnattr_t local_attributes; int local_ready=0;
    if(image->kernel_bound) {
        if(!attributes) {
            error=posix_spawnattr_init(&local_attributes);
            if(error)return error;
            attributes=&local_attributes;local_ready=1;
        }
        error=sosix_darwin_amfi_attach(attributes,image->cdhash,image->amfi_requirement);
    }
    if(!error) {
        SOSIX_DARWIN_IMAGE_BEFORE_SPAWN(image);
        error=posix_spawn(pid,image->path,actions,attributes,argv,environment);
    }
    if(local_ready)posix_spawnattr_destroy(&local_attributes);
    return error;
}

static int sosix_darwin_image_close(SosixDarwinImage *image, uint64_t generation) {
    if (!image || !generation || image->generation != generation || image->fd < 0) return ESTALE;
    int error = 0;
    if (close(image->fd)) error = errno;
    if (unlink(image->path) && !error) error = errno;
    if (rmdir(image->directory) && !error) error = errno;
    memset(image, 0, sizeof(*image)); image->fd = -1; return error;
}
#endif
#endif
