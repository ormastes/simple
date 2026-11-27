/* Actual configured XFS project quota provider. Never substitutes statvfs for
 * enforcement and never changes administrator quota or permission policy. */
#ifndef SIMPLE_WORKSPACE_STORAGE_LINUX_PRIVATE_H
#define SIMPLE_WORKSPACE_STORAGE_LINUX_PRIVATE_H
#include <dirent.h>
#include <fcntl.h>
#include <linux/dqblk_xfs.h>
#include <linux/fs.h>
#include <linux/magic.h>
#include <linux/quota.h>
#include <sys/ioctl.h>
#include <sys/stat.h>
#include <sys/statfs.h>
#include <sys/syscall.h>
#include <unistd.h>

typedef struct {
    int parent_fd, workspace_fd;
    uint64_t device, inode;
    uint32_t project;
} WsNativeV1;

static int ws_quota_v1(int fd, unsigned command, uint32_t project, void* value) {
#ifdef SYS_quotactl_fd
    if (syscall(SYS_quotactl_fd, fd, command, project, value) == 0) return 0;
    return errno ? errno : EIO;
#else
    (void)fd; (void)command; (void)project; (void)value; return ENOTSUP;
#endif
}
static int ws_linux_measure_v1(WsNativeV1* native, int64_t hard,
        int64_t* used, int64_t* inodes) {
    struct fs_quota_statv state = {.qs_version = FS_QSTATV_VERSION1};
    int error = ws_quota_v1(native->parent_fd, QCMD(Q_XGETQSTATV, PRJQUOTA), 0, &state);
    if (error) return error;
    unsigned required = FS_QUOTA_PDQ_ACCT | FS_QUOTA_PDQ_ENFD;
    if (state.qs_version != FS_QSTATV_VERSION1 || (state.qs_flags & required) != required)
        return ENOTSUP;
    fs_disk_quota_t quota = {.d_version = FS_DQUOT_VERSION};
    error = ws_quota_v1(native->parent_fd, QCMD(Q_XGETQUOTA, PRJQUOTA), native->project, &quota);
    if (error) return error;
    if (quota.d_version != FS_DQUOT_VERSION || quota.d_id != native->project ||
            !(quota.d_flags & FS_PROJ_QUOTA) || hard <= 0 || hard % 512 ||
            quota.d_blk_hardlimit != (uint64_t)hard / 512 ||
            quota.d_bcount > INT64_MAX / 512 || quota.d_icount > INT64_MAX)
        return ESTALE;
    *used = (int64_t)quota.d_bcount * 512;
    *inodes = (int64_t)quota.d_icount;
    return 0;
}
static int ws_linux_ids_v1(int parent, int child, char* pool, size_t pool_size,
        char* workspace, size_t workspace_size, uint32_t project) {
    struct statfs fs;
    struct stat p, c;
    struct statx sx;
    struct fsxattr attributes;
    int generation = 0;
    memset(&sx, 0, sizeof(sx)); memset(&attributes, 0, sizeof(attributes));
    if (fstat(parent, &p) || fstat(child, &c) || fstatfs(parent, &fs)) return errno;
    if (!S_ISDIR(p.st_mode) || !S_ISDIR(c.st_mode) || p.st_dev != c.st_dev ||
            p.st_uid != geteuid() || (p.st_mode & 0022) || fs.f_type != XFS_SUPER_MAGIC)
        return EPERM;
#if defined(SYS_statx) && defined(STATX_MNT_ID)
    if (syscall(SYS_statx, parent, "", AT_EMPTY_PATH | AT_SYMLINK_NOFOLLOW,
            STATX_MNT_ID, &sx) != 0 || !(sx.stx_mask & STATX_MNT_ID)) return ENOTSUP;
#else
    return ENOTSUP;
#endif
    if (ioctl(child, FS_IOC_FSGETXATTR, &attributes) ||
            ioctl(child, FS_IOC_GETVERSION, &generation)) return errno;
    if (attributes.fsx_projid != project || !(attributes.fsx_xflags & FS_XFLAG_PROJINHERIT))
        return ESTALE;
    int a = snprintf(pool, pool_size, "xfs:%llu:%llu:%08x:%08x",
        (unsigned long long)p.st_dev, (unsigned long long)sx.stx_mnt_id,
        (unsigned)fs.f_fsid.__val[0], (unsigned)fs.f_fsid.__val[1]);
    int b = snprintf(workspace, workspace_size, "inode:%llu:%llu:%u:%llu",
        (unsigned long long)c.st_dev, (unsigned long long)c.st_ino,
        (unsigned)generation, (unsigned long long)c.st_uid);
    return a > 0 && (size_t)a < pool_size && b > 0 && (size_t)b < workspace_size ? 0 : EOVERFLOW;
}
static void ws_native_close_v1(WsNativeV1* native) {
    if (native->workspace_fd >= 0) close(native->workspace_fd);
    if (native->parent_fd >= 0) close(native->parent_fd);
    native->workspace_fd = native->parent_fd = -1;
}
static int ws_native_open_v1(WsNativeV1* native, const char* kind, const char* parent,
        const char* leaf, const char* expected_pool, const char* expected_workspace,
        uint32_t project, int64_t hard, int64_t* used, int64_t* inodes) {
    native->parent_fd = native->workspace_fd = -1; native->project = project;
    if (strcmp(kind, "linux-xfs-project-v1") || parent[0] != '/' || !project) return ENOTSUP;
    native->parent_fd = open(parent, O_RDONLY | O_DIRECTORY | O_CLOEXEC | O_NOFOLLOW);
    if (native->parent_fd < 0) return errno;
    native->workspace_fd = openat(native->parent_fd, leaf, O_RDONLY | O_DIRECTORY | O_CLOEXEC | O_NOFOLLOW);
    if (native->workspace_fd < 0) return errno;
    char pool[256], workspace[256];
    int error = ws_linux_ids_v1(native->parent_fd, native->workspace_fd,
        pool, sizeof(pool), workspace, sizeof(workspace), project);
    if (error) return error;
    if (strcmp(pool, expected_pool) || strcmp(workspace, expected_workspace)) return ESTALE;
    struct stat st;
    if (fstat(native->workspace_fd, &st)) return errno;
    native->device = st.st_dev; native->inode = st.st_ino;
    return ws_linux_measure_v1(native, hard, used, inodes);
}
static int ws_native_observe_v1(WsNativeV1* native, const char* leaf,
        const char* pool, const char* workspace, int64_t hard, int64_t* used, int64_t* inodes) {
    if (native->workspace_fd < 0) return ESTALE;
    struct stat current;
    if (fstatat(native->parent_fd, leaf, &current, AT_SYMLINK_NOFOLLOW)) return errno;
    if (!S_ISDIR(current.st_mode) || current.st_dev != native->device || current.st_ino != native->inode)
        return ESTALE;
    char observed_pool[256], observed_workspace[256];
    int error = ws_linux_ids_v1(native->parent_fd, native->workspace_fd,
        observed_pool, sizeof(observed_pool), observed_workspace, sizeof(observed_workspace), native->project);
    if (error) return error;
    if (strcmp(pool, observed_pool) || strcmp(workspace, observed_workspace)) return ESTALE;
    return ws_linux_measure_v1(native, hard, used, inodes);
}
static int ws_native_release_if_absent_v1(WsNativeV1* native, const char* leaf,
        int64_t hard, int64_t* used, int64_t* inodes) {
    struct stat st;
    if (fstatat(native->parent_fd, leaf, &st, AT_SYMLINK_NOFOLLOW) == 0) return EBUSY;
    if (errno != ENOENT) return errno;
    if (native->workspace_fd >= 0) {
        if (fstat(native->workspace_fd, &st)) return errno;
        if (st.st_nlink != 0 || st.st_dev != native->device || st.st_ino != native->inode) return ESTALE;
        /* The exact inode was actually unlinked. Drop only our descriptor so
         * its quota charge can drain; keep parent/project authority on error. */
        close(native->workspace_fd); native->workspace_fd = -1;
    }
    int error = ws_linux_measure_v1(native, hard, used, inodes);
    if (error) return error;
    if (*used || *inodes) return EBUSY;
    ws_native_close_v1(native);
    return 0;
}
#endif
