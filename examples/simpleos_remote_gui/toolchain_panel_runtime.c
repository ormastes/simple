#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>

#ifndef TOOLCHAIN_NAME
#define TOOLCHAIN_NAME "Toolchain"
#endif

#ifndef TOOLCHAIN_VERSION_PATH
#define TOOLCHAIN_VERSION_PATH "/SYS/VERSION.TXT"
#endif

#ifndef TOOLCHAIN_MANIFEST_PATH
#define TOOLCHAIN_MANIFEST_PATH "/SYS/MANIFEST.TXT"
#endif

#ifndef TOOLCHAIN_PRIMARY_PATH
#define TOOLCHAIN_PRIMARY_PATH "/usr/bin/tool"
#endif

#ifndef TOOLCHAIN_SECONDARY_PATH
#define TOOLCHAIN_SECONDARY_PATH ""
#endif

static int _toolchain_file_exists(const char *path) {
    return path != NULL && path[0] != '\0' && access(path, F_OK) == 0;
}

static void _toolchain_read_first_line(const char *path, char *out, size_t cap) {
    int fd;
    ssize_t n;
    size_t i;
    if (cap == 0) {
        return;
    }
    out[0] = '\0';
    if (!_toolchain_file_exists(path)) {
        return;
    }
    fd = open(path, O_RDONLY);
    if (fd < 0) {
        return;
    }
    n = read(fd, out, cap - 1);
    close(fd);
    if (n <= 0) {
        out[0] = '\0';
        return;
    }
    out[(size_t)n] = '\0';
    for (i = 0; out[i] != '\0'; ++i) {
        if (out[i] == '\n' || out[i] == '\r') {
            out[i] = '\0';
            break;
        }
    }
}

static const char *toolchain_runtime_content(int argc, char **argv) {
    static char content[1600];
    char version[256];
    const int has_primary = _toolchain_file_exists(TOOLCHAIN_PRIMARY_PATH);
    const int has_secondary = (TOOLCHAIN_SECONDARY_PATH[0] == '\0') || _toolchain_file_exists(TOOLCHAIN_SECONDARY_PATH);
    (void)argc;
    (void)argv;

    _toolchain_read_first_line(TOOLCHAIN_VERSION_PATH, version, sizeof(version));
    if (version[0] == '\0') {
        snprintf(version, sizeof(version), "version metadata missing");
    }

    snprintf(
        content,
        sizeof(content),
        "%s\n\n[Filesystem Payload]\nprimary: %s (%s)\nsecondary: %s (%s)\nmanifest: %s\n\n[Version]\n%s",
        TOOLCHAIN_NAME,
        TOOLCHAIN_PRIMARY_PATH,
        has_primary ? "present" : "missing",
        TOOLCHAIN_SECONDARY_PATH[0] == '\0' ? "(none)" : TOOLCHAIN_SECONDARY_PATH,
        has_secondary ? "present" : "missing",
        TOOLCHAIN_MANIFEST_PATH,
        version
    );
    return content;
}

static int toolchain_pre_window_hook(const char *app_id) {
    char version[256];
    if (!_toolchain_file_exists(TOOLCHAIN_PRIMARY_PATH)) {
        printf("[desktop-e2e] toolchain-launch:fail app=%s reason=missing-primary path=%s\n", app_id, TOOLCHAIN_PRIMARY_PATH);
        return 21;
    }
    if (TOOLCHAIN_SECONDARY_PATH[0] != '\0' && !_toolchain_file_exists(TOOLCHAIN_SECONDARY_PATH)) {
        printf("[desktop-e2e] toolchain-launch:fail app=%s reason=missing-secondary path=%s\n", app_id, TOOLCHAIN_SECONDARY_PATH);
        return 22;
    }
    if (!_toolchain_file_exists(TOOLCHAIN_MANIFEST_PATH)) {
        printf("[desktop-e2e] toolchain-launch:fail app=%s reason=missing-manifest path=%s\n", app_id, TOOLCHAIN_MANIFEST_PATH);
        return 23;
    }
    _toolchain_read_first_line(TOOLCHAIN_VERSION_PATH, version, sizeof(version));
    if (version[0] == '\0') {
        printf("[desktop-e2e] toolchain-launch:fail app=%s reason=missing-version path=%s\n", app_id, TOOLCHAIN_VERSION_PATH);
        return 24;
    }
    if (TOOLCHAIN_SECONDARY_PATH[0] != '\0') {
        printf("[desktop-e2e] toolchain-launch:ok app=%s tool=%s aux=%s version=%s\n", app_id, TOOLCHAIN_PRIMARY_PATH, TOOLCHAIN_SECONDARY_PATH, version);
    } else {
        printf("[desktop-e2e] toolchain-launch:ok app=%s tool=%s version=%s\n", app_id, TOOLCHAIN_PRIMARY_PATH, version);
    }
    return 0;
}
