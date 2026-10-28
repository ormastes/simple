/* Private POSIX cwd pin implementation. Requires runtime array and owned helpers. */
static int pov4_canonical_directory(const char* value) {
    size_t length;
    if (!value || value[0] != '/' || (length = strlen(value)) <= 1 ||
        value[length - 1] == '/') return 0;
    for (size_t i = 0; i < length; i++) {
        if (value[i] == '/' && i + 1 < length && value[i + 1] == '/') return 0;
        if (value[i] == '/' && i + 2 < length && value[i + 1] == '.' &&
            (value[i + 2] == '/' || (value[i + 2] == '.' &&
             (i + 3 == length || value[i + 3] == '/')))) return 0;
    }
    return 1;
}


typedef struct Pov4CwdPin {
    uint64_t handle;
    int fd;
    char* canonical_path;
    uint8_t digest[POV4_DIGEST_BYTES];
} Pov4CwdPin;

static Pov4CwdPin pov4_cwd_pins[POV4_CWD_PINS];
static pthread_mutex_t pov4_cwd_lock = PTHREAD_MUTEX_INITIALIZER;

static void pov4_store_u64_le(uint8_t* out, uint64_t value) {
    for (unsigned i = 0; i < 8; i++) out[i] = (uint8_t)(value >> (8 * i));
}

static int pov4_directory_digest(int fd, uint8_t digest[POV4_DIGEST_BYTES]) {
    struct stat info;
    if (fstat(fd, &info) != 0 || !S_ISDIR(info.st_mode)) {
        if (errno == 0) errno = ENOTDIR;
        return 0;
    }
    uint8_t identity[32] = {'P','O','V','4','C','W','D',0};
    pov4_store_u64_le(identity + 8, (uint64_t)info.st_dev);
    pov4_store_u64_le(identity + 16, (uint64_t)info.st_ino);
    pov4_store_u64_le(identity + 24, (uint64_t)info.st_mode);
    owned_sha256(identity, sizeof(identity), digest);
    return 1;
}

static int pov4_mint_positive(uint64_t* value) {
#if (defined(__linux__) && defined(SYS_getrandom)) || defined(__APPLE__)
    for (int attempt = 0; attempt < 32; attempt++) {
        uint64_t candidate = 0;
        ssize_t got = RT_OWNED_TOKEN_FILL(&candidate, sizeof(candidate));
        candidate &= (uint64_t)INT64_MAX;
        if (got == (ssize_t)sizeof(candidate) && candidate != 0) {
            *value = candidate;
            return 1;
        }
    }
    errno = EAGAIN;
    return 0;
#else
    (void)value;
    errno = ENOTSUP;
    return 0;
#endif
}

int64_t rt_process_observation_v4_pin_cwd_value(const char* path_data,
                                                 uint64_t path_len) {
#if !defined(__linux__) && !defined(__APPLE__)
    (void)path_data; (void)path_len; errno = ENOTSUP; return 0;
#else
    if (!path_data || path_len == 0 || path_len > POV4_MAX_TEXT_BYTES ||
        path_len > SIZE_MAX - 1) { errno = EINVAL; return 0; }
    char* path = (char*)RT_OWNED_HOST_MALLOC((size_t)path_len + 1);
    if (!path) { errno = ENOMEM; return 0; }
    memcpy(path, path_data, (size_t)path_len); path[path_len] = '\0';
    if (memchr(path, '\0', (size_t)path_len) || !pov4_canonical_directory(path)) {
        RT_OWNED_HOST_FREE(path); errno = EINVAL; return 0;
    }
    char resolved[PATH_MAX];
    if (!realpath(path, resolved) || strcmp(path, resolved) != 0) {
        int saved = errno ? errno : EINVAL;
        RT_OWNED_HOST_FREE(path); errno = saved; return 0;
    }
#if defined(RT_PROCESS_OBSERVATION_V4_TESTING) && defined(POV4_CWD_TEST_AFTER_REALPATH)
    POV4_CWD_TEST_AFTER_REALPATH();
#endif
    /* O_NOFOLLOW on a full path protects only its final component; walk from
     * root so no intermediate component can be replaced by a followed symlink. */
    int fd = open("/", O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
    if (fd >= 0) {
        char* component = path + 1;
        while (*component) {
            char* slash = strchr(component, '/');
            if (slash) *slash = '\0';
            int next = openat(fd, component, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
            int saved = errno;
            if (slash) *slash = '/';
            close(fd);
            fd = next;
            if (fd < 0) { errno = saved; break; }
#if defined(RT_PROCESS_OBSERVATION_V4_TESTING) && defined(POV4_CWD_TEST_AFTER_COMPONENT)
            POV4_CWD_TEST_AFTER_COMPONENT(component, slash);
#endif
            if (!slash) break;
            component = slash + 1;
        }
    }
    uint8_t digest[POV4_DIGEST_BYTES];
    if (fd < 0 || !pov4_directory_digest(fd, digest)) {
        int saved = errno ? errno : EIO;
        if (fd >= 0) close(fd);
        RT_OWNED_HOST_FREE(path); errno = saved; return 0;
    }
    if (pthread_mutex_lock(&pov4_cwd_lock) != 0) {
        close(fd); RT_OWNED_HOST_FREE(path); errno = EBUSY; return 0;
    }
    int free_index = -1;
    for (int i = 0; i < POV4_CWD_PINS; i++)
        if (pov4_cwd_pins[i].handle == 0) { free_index = i; break; }
    uint64_t handle = 0;
    if (free_index >= 0) {
        for (int attempt = 0; attempt < 32 && handle == 0; attempt++) {
            uint64_t candidate = 0;
            if (!pov4_mint_positive(&candidate)) break;
            int duplicate = 0;
            for (int i = 0; i < POV4_CWD_PINS; i++)
                if (pov4_cwd_pins[i].handle == candidate) duplicate = 1;
            if (!duplicate) handle = candidate;
        }
    }
    if (free_index < 0 || handle == 0) {
        pthread_mutex_unlock(&pov4_cwd_lock);
        close(fd); RT_OWNED_HOST_FREE(path);
        errno = free_index < 0 ? EAGAIN : (errno ? errno : EAGAIN); return 0;
    }
    Pov4CwdPin* pin = &pov4_cwd_pins[free_index];
    pin->handle = handle; pin->fd = fd; pin->canonical_path = path;
    memcpy(pin->digest, digest, sizeof(pin->digest));
    pthread_mutex_unlock(&pov4_cwd_lock);
    return (int64_t)handle;
#endif
}

static int pov4_acquire_cwd(uint64_t handle, const char* canonical_path,
                            const uint8_t digest[POV4_DIGEST_BYTES]) {
    if (handle == 0 || pthread_mutex_lock(&pov4_cwd_lock) != 0) {
        errno = handle == 0 ? ESTALE : EBUSY; return -1;
    }
    int duplicate = -1;
    int matched = 0;
    for (int i = 0; i < POV4_CWD_PINS; i++) {
        Pov4CwdPin* pin = &pov4_cwd_pins[i];
        if (pin->handle == handle && canonical_path &&
            strcmp(pin->canonical_path, canonical_path) == 0 &&
            memcmp(pin->digest, digest, POV4_DIGEST_BYTES) == 0) {
            matched = 1;
            duplicate = fcntl(pin->fd, F_DUPFD_CLOEXEC, 3);
            break;
        }
    }
    pthread_mutex_unlock(&pov4_cwd_lock);
    if (duplicate < 0) { if (!matched) errno = ESTALE; return -1; }
    uint8_t current[POV4_DIGEST_BYTES];
    if (!pov4_directory_digest(duplicate, current) ||
        memcmp(current, digest, POV4_DIGEST_BYTES) != 0) {
        int saved = errno ? errno : ESTALE; close(duplicate); errno = saved; return -1;
    }
    return duplicate;
}

SplArray* rt_process_observation_v4_cwd_digest_value(int64_t handle) {
    uint8_t digest[POV4_DIGEST_BYTES]; int found = 0;
    if (handle > 0 && pthread_mutex_lock(&pov4_cwd_lock) == 0) {
        for (int i = 0; i < POV4_CWD_PINS; i++) if (pov4_cwd_pins[i].handle == (uint64_t)handle) {
            memcpy(digest, pov4_cwd_pins[i].digest, sizeof(digest)); found = 1; break;
        }
        pthread_mutex_unlock(&pov4_cwd_lock);
    }
    return owned_adapter_bytes((const char*)digest, found ? sizeof(digest) : 0);
}

int rt_process_observation_v4_close_cwd_value(int64_t handle) {
    int fd = -1; char* path = NULL;
    if (handle <= 0 || pthread_mutex_lock(&pov4_cwd_lock) != 0) return 0;
    for (int i = 0; i < POV4_CWD_PINS; i++) if (pov4_cwd_pins[i].handle == (uint64_t)handle) {
        fd = pov4_cwd_pins[i].fd; path = pov4_cwd_pins[i].canonical_path;
        memset(&pov4_cwd_pins[i], 0, sizeof(pov4_cwd_pins[i])); break;
    }
    pthread_mutex_unlock(&pov4_cwd_lock);
    if (fd < 0) return 0;
    close(fd); RT_OWNED_HOST_FREE(path); return 1;
}
