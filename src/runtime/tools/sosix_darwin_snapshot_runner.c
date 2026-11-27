/* Native process-group runner. This is deliberately NOT the sealed V4 ABI.
 * Callers explicitly select cooperative or AMFI-bound image admission.
 * Build: cc -std=c11 -Wno-deprecated-declarations this-file.c -o runner */
#define _DARWIN_C_SOURCE
#ifdef __APPLE__
#include "../runtime_sosix_darwin_process_private.h"
#include <inttypes.h>

extern char **environ;
static volatile sig_atomic_t interrupted;
static void request_cancel(int signal_number) { interrupted = signal_number; }

static int decimal(const char *text, uint64_t limit, uint64_t *value) {
    if (!text || !*text) return 0;
    uint64_t n = 0;
    for (; *text; text++) {
        if (*text < '0' || *text > '9') return 0;
        unsigned digit = (unsigned)(*text - '0');
        if (n > limit / 10 || (n == limit / 10 && digit > limit % 10)) return 0;
        n = n * 10 + digit;
    }
    *value = n; return 1;
}

static int usage(void) {
    fputs("usage: runner --capabilities | --profile trusted-snapshot-group "
          "--cwd DIRECTORY [--wall-ms N] [--output-limit N] -- MACH_O [ARG ...]\n"
          "       runner --profile bound-image-group --sha256 DIGEST --cwd DIRECTORY "
          "[--wall-ms N] [--output-limit N] -- MACH_O [ARG ...]\n", stderr);
    return 64;
}

int main(int argc, char **argv) {
    if(argc==4 && !strcmp(argv[1],"--capabilities") && !strcmp(argv[2],"--profile") && !strcmp(argv[3],"bound-image-group")) {
        posix_spawnattr_t probe;unsigned char hash[20]={0},bytes[82];
        int error=posix_spawnattr_init(&probe);
        if(!error){error=sosix_darwin_amfi_attach(&probe,hash,bytes);posix_spawnattr_destroy(&probe);}
        printf("profile: \"bound-image-group\"\namfi_spi_available: %s\nsource_sha256_required: true\n"
               "system_libraries_only: true\nprocess_group: true\ncomplete_descendant_tree: false\nsealed_v4: false\n",error?"false":"true");
        return error?78:0;
    }
    if (argc == 2 && !strcmp(argv[1], "--capabilities")) {
        puts("profile: \"trusted-snapshot-group\"\nsnapshot: true\nprocess_group: true\n"
             "immutable_executable: false\ncomplete_descendant_tree: false\nsealed_v4: false");
        return 0;
    }
    const char *profile = NULL, *directory = NULL,*digest_text=NULL;
    uint64_t wall_ms = 1000, output_limit = 1024 * 1024;
    int command = 0;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--")) { command = i + 1; break; }
        if (i + 1 >= argc) return usage();
        const char *option = argv[i++], *value = argv[i];
        if (!strcmp(option, "--profile") && !profile) profile = value;
        else if (!strcmp(option, "--cwd") && !directory) directory = value;
        else if (!strcmp(option,"--sha256") && !digest_text) digest_text=value;
        else if (!strcmp(option, "--wall-ms")) {
            if (!decimal(value, 86400000, &wall_ms) || !wall_ms) return usage();
        } else if (!strcmp(option, "--output-limit")) {
            if (!decimal(value, 16 * 1024 * 1024, &output_limit)) return usage();
        } else return usage();
    }
    /* Admission precedes file acquisition, copying, and every process action. */
    int bound=profile && !strcmp(profile,"bound-image-group");
    if (!profile || (!bound && strcmp(profile, "trusted-snapshot-group"))) {
        fputs("unsupported profile: complete descendant tree is unavailable on this native provider\n", stderr);
        return 64;
    }
    if (!directory || !command || command >= argc) return usage();
    unsigned char expected[32];
    if(bound) {
        if(!digest_text || strlen(digest_text)!=64)return usage();
        for(size_t i=0;i<32;i++) {
            unsigned value=0;
            for(size_t j=0;j<2;j++) {
                unsigned char c=(unsigned char)digest_text[i*2+j];
                if(c>='0'&&c<='9')value=value*16+c-'0';
                else if(c>='a'&&c<='f')value=value*16+c-'a'+10;
                else return usage();
            }
            expected[i]=(unsigned char)value;
        }
        posix_spawnattr_t probe;unsigned char zero[20]={0},bytes[82];int error=posix_spawnattr_init(&probe);
        if(!error){error=sosix_darwin_amfi_attach(&probe,zero,bytes);posix_spawnattr_destroy(&probe);}
        if(error){fputs("bound runner AMFI unavailable\n",stderr);return 78;}
    } else if(digest_text)return usage();
    int cwd = open(directory, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    if (cwd < 0) { perror("snapshot runner cwd"); return 125; }
    /* Opening a FIFO must not block before the image owner's regular-file
     * validation. O_NONBLOCK does not change reads from a regular executable. */
    int source = open(argv[command], O_RDONLY | O_CLOEXEC | O_NOFOLLOW | O_NONBLOCK);
    if (source < 0) { perror("snapshot runner executable"); close(cwd); return 125; }
    SosixDarwinImage image;
    int error = bound?sosix_darwin_image_create_bound(source,expected,&image):sosix_darwin_image_create(source, &image); close(source);
    if (error) { close(cwd); fprintf(stderr, "snapshot runner image: %s\n", strerror(error)); return 125; }

    struct sigaction action; memset(&action, 0, sizeof(action));
    action.sa_handler = request_cancel; sigemptyset(&action.sa_mask);
    if (sigaction(SIGINT, &action, NULL) || sigaction(SIGTERM, &action, NULL)) {
        error = errno; close(cwd); sosix_darwin_image_close(&image, image.generation);
        fprintf(stderr, "snapshot runner signals: %s\n", strerror(error)); return 125;
    }
    signal(SIGPIPE, SIG_IGN);
    /* SIG_IGN survives exec; the CLI owns reaping even when its parent ignores
     * SIGCHLD. The lower-level component intentionally leaves this to callers. */
    action.sa_handler = SIG_DFL;
    if (sigaction(SIGCHLD, &action, NULL)) {
        error = errno; close(cwd); sosix_darwin_image_close(&image, image.generation);
        fprintf(stderr, "snapshot runner SIGCHLD: %s\n", strerror(error)); return 125;
    }
    SosixDarwinProcess owner;
    SosixDarwinProcessLimits limits = {(int64_t)wall_ms * 1000000LL,
        20000000LL, 2000000000LL, (size_t)output_limit, (size_t)output_limit};
    error = sosix_darwin_process_start(&owner, &image, image.generation, cwd,
        &argv[command], environ, limits);
    close(cwd);
    if (error) {
        sosix_darwin_image_close(&image, image.generation);
        fprintf(stderr, "snapshot runner spawn: %s\n", strerror(error)); return 125;
    }
    while (!owner.frozen) {
        if (interrupted) owner.cancel_requested = 1;
        error = sosix_darwin_process_poll(&owner, owner.generation, 10000000LL);
        if (error == EINTR) { error = 0; continue; }
        if (error) break;
    }
    int result = 125;
    if (!error) {
        if (owner.stdout_error || owner.stderr_error) error = EIO;
        if (fwrite(owner.stdout_bytes, 1, owner.stdout_kept, stdout) != owner.stdout_kept ||
            fwrite(owner.stderr_bytes, 1, owner.stderr_kept, stderr) != owner.stderr_kept ||
            fflush(stdout) || fflush(stderr)) error = EIO;
        if (owner.timed_out) result = 124;
        else if (interrupted) result = 128 + interrupted;
        else if (WIFEXITED(owner.wait_status)) result = WEXITSTATUS(owner.wait_status);
        else if (WIFSIGNALED(owner.wait_status)) result = 128 + WTERMSIG(owner.wait_status);
        int ack = sosix_darwin_process_ack(&owner, owner.generation);
        if (ack && !error) error = ack;
    } else {
        /* Error is never a completed-group receipt. Best-effort group kill,
         * then reap our exact child before releasing the snapshot. Escaped
         * descendants are outside this explicitly cooperative profile. */
        if (!owner.reaped) {
            (void)kill(-owner.pid, SIGKILL);
            while (waitpid(owner.pid, NULL, 0) < 0 && errno == EINTR) {}
        }
        if (owner.stdout_fd >= 0) close(owner.stdout_fd);
        if (owner.stderr_fd >= 0) close(owner.stderr_fd);
        free(owner.stdout_bytes); free(owner.stderr_bytes);
    }
    int close_error = sosix_darwin_image_close(&image, image.generation);
    if (!error) error = close_error;
    if (error) { fprintf(stderr, "snapshot runner failed: %s\n", strerror(error)); return 125; }
    return result;
}
#else
#include <stdio.h>
int main(void) { fputs("UNAVAILABLE: native Darwin snapshot runner requires macOS\n", stderr); return 77; }
#endif
