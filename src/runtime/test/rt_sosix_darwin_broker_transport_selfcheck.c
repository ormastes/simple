#include "../runtime_sosix_darwin_broker_transport_private.h"
#include <assert.h>
#include <fcntl.h>
#include <poll.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <mach-o/dyld.h>
#include <crt_externs.h>

/* This marker runs before main: failed binding must prevent even constructors. */
__attribute__((constructor)) static void entered(void) {
    int argc = *_NSGetArgc(); char **argv = *_NSGetArgv();
    if (argc != 5 || strcmp(argv[1], SOSIX_DARWIN_BROKER_MODE)) return;
    char path[PATH_MAX]; snprintf(path, sizeof(path), "%s.entered", argv[2]);
    int fd = open(path, O_CREAT | O_WRONLY | O_TRUNC, 0600);
    if (fd >= 0) { (void)write(fd, "entered", 7); close(fd); }
}
static void pause_ms(unsigned ms) { struct timespec delay = {ms / 1000, (ms % 1000)*1000000L}; nanosleep(&delay, NULL); }
static int connect_to(const char *endpoint) {
    int fd = socket(AF_UNIX, SOCK_STREAM, 0); assert(fd >= 0);
    struct sockaddr_un address = {.sun_family = AF_UNIX};
    assert(strlen(endpoint) < sizeof(address.sun_path)); strcpy(address.sun_path, endpoint);
    if (connect(fd, (struct sockaddr *)&address, sizeof(address))) { close(fd); return -1; }
    return fd;
}
static ssize_t read_byte(int fd, char *byte) {
    struct pollfd p = {fd, POLLIN, 0};
    int n; do n = poll(&p, 1, 3000); while (n < 0 && errno == EINTR);
    if (n != 1 || !(p.revents & (POLLIN | POLLHUP))) return -1;
    return read(fd, byte, 1);
}
static int accept_for(int listener, int ms) {
    struct pollfd p = {listener, POLLIN, 0};
    int n; do n = poll(&p, 1, ms); while(n < 0 && errno == EINTR);
    int fd = n == 1 && (p.revents & POLLIN) ? accept(listener, NULL, NULL) : -1;
    return fd;
}
/* A hostile same-UID actor can recreate a label. This deliberately bypasses
 * the public primitive's generated-label policy to test pinned incarnation. */
static void replace_registration(SosixDarwinBrokerTransport *job, int hostile_environment) {
    launch_data_t request = launch_data_alloc(LAUNCH_DATA_DICTIONARY);
    launch_data_t description = launch_data_alloc(LAUNCH_DATA_DICTIONARY);
    launch_data_t args = launch_data_alloc(LAUNCH_DATA_ARRAY);
    launch_data_t constraint = launch_data_alloc(LAUNCH_DATA_DICTIONARY);
    assert(request && description && args && constraint);
    for (size_t i = 0; i < 5; ++i)
        assert(launch_data_array_set_index(args, launch_data_new_string(sosix_darwin_broker_argument(job, i)), i));
    assert(!sosix_darwin_broker_put(description, "Label", launch_data_new_string(job->label)));
    assert(!sosix_darwin_broker_put(description, "ProgramArguments", args));
    assert(!sosix_darwin_broker_put(description, "RunAtLoad", launch_data_new_bool(1)));
    assert(!sosix_darwin_broker_put(description, "LaunchOnlyOnce", launch_data_new_bool(1)));
    assert(!sosix_darwin_broker_put(constraint, "cdhash", launch_data_new_opaque(job->cdhash, 20)));
    assert(!sosix_darwin_broker_put(description, "SpawnConstraint", constraint));
    if (hostile_environment) {
        launch_data_t env = launch_data_alloc(LAUNCH_DATA_DICTIONARY); assert(env);
        assert(!sosix_darwin_broker_put(env, "SOSIX_BROKER_ADVERSARIAL", launch_data_new_string("injected")));
        assert(!sosix_darwin_broker_put(description, "EnvironmentVariables", env));
    }
    assert(!sosix_darwin_broker_put(request, "SubmitJob", description));
    launch_data_t reply = launch_msg(request);
    assert(!sosix_darwin_broker_reply_error(reply));
    launch_data_free(reply); launch_data_free(request); job->submitted = 1;
}
static void remove_job(SosixDarwinBrokerTransport *job) {
    int e = sosix_darwin_broker_remove_registration(job);
    assert(e == 0 || e == EINPROGRESS || e == ESRCH);
    for (int i = 0; i < 100 && job->submitted; ++i) {
        pause_ms(20); e = sosix_darwin_broker_remove_registration(job);
        assert(e == 0 || e == EINPROGRESS || e == ESRCH);
    }
    assert(!job->submitted);
}
int main(int argc, char **argv) {
    if (argc == 5 && !strcmp(argv[1], SOSIX_DARWIN_BROKER_MODE)) {
        int fd = connect_to(argv[2]); if (fd < 0) return 91;
        audit_token_t token; SosixDarwinProcessIdentity identity;
        int e = sosix_darwin_broker_peer_identity(fd, (pid_t)strtol(argv[3], NULL, 10),
            (uint32_t)strtoul(argv[4], NULL, 10), &token, &identity);
        if (e) { close(fd); return 92; }
        char byte = getenv("SOSIX_BROKER_ADVERSARIAL") ? 'E' : 'A'; if (write(fd, &byte, 1) != 1) return 93;
        if (read_byte(fd, &byte) == 1 && byte == 'X') {
            char *args[] = {"/bin/sleep", "3", NULL}; execv(args[0], args); return 94;
        }
        close(fd); return 0;
    }
    assert(argc == 4);
    unsigned char hash[20]; assert(strlen(argv[1]) == 40);
    for (size_t i = 0; i < 20; ++i) { unsigned value; assert(sscanf(argv[1]+2*i, "%2x", &value)==1); hash[i] = (unsigned char)value; }
    char endpoint[104]; assert(snprintf(endpoint, sizeof(endpoint), "%s/sock", argv[2]) < (int)sizeof(endpoint));
    int listener = socket(AF_UNIX, SOCK_STREAM, 0); assert(listener >= 0);
    struct sockaddr_un address = {.sun_family = AF_UNIX}; strcpy(address.sun_path, endpoint);
    assert(bind(listener, (struct sockaddr *)&address, sizeof(address)) == 0); assert(listen(listener, 8) == 0);
    char marker[PATH_MAX]; snprintf(marker, sizeof(marker), "%s.entered", endpoint);
    SosixDarwinBrokerTransport job = {0};
    assert(sosix_darwin_broker_submit(&job, argv[0], endpoint, hash) == 0);
    assert(sosix_darwin_broker_submit(&job, argv[0], endpoint, hash) == EALREADY);
    int peer = accept_for(listener, 4000); assert(peer >= 0);
    int e = sosix_darwin_broker_observe_peer(&job, peer);
    if (e) fprintf(stderr, "authenticate: %d\n", e);
    assert(e == 0); assert(job.peer_observed);
    char byte; assert(read_byte(peer, &byte) == 1 && byte == 'A');
    assert(access(marker, F_OK) == 0); unlink(marker);
    puts("mutual_kernel_peer_identity: observed");
    audit_token_t token; SosixDarwinProcessIdentity identity;
    assert(sosix_darwin_broker_peer_identity(peer, job.peer_pid, (uint32_t)job.peer_identity.pid_version + 1, &token, &identity) == EACCES);
    assert(sosix_darwin_broker_peer_identity(peer, getpid(), (uint32_t)job.peer_identity.pid_version, &token, &identity) == EACCES);
    unsigned char wrong[20]; memcpy(wrong, hash, 20); wrong[0] ^= 1;
    assert(sosix_darwin_broker_peer_cdhash(&job.peer_token, wrong) == EACCES);
    token = job.peer_token; token.val[7]++;
    assert(sosix_darwin_broker_peer_cdhash(&token, hash) != 0);
    puts("wrong_pid_version_and_cdhash: rejected");
    SosixDarwinBrokerTransport altered = job;
    altered.controller_version[0] = altered.controller_version[0] == '1' ? '2' : '1';
    assert(sosix_darwin_broker_observe_peer(&altered, peer) == EACCES);
    altered = job; altered.peer_identity.unique_id++;
    assert(sosix_darwin_broker_observe_peer(&altered, peer) == ESTALE);
    puts("getjob_argument_and_incarnation_substitution: rejected");
    /* Same UID and exact same code image are insufficient for an unrelated peer. */
    pid_t impostor = fork(); assert(impostor >= 0);
    if (!impostor) { close(peer); int fd = connect_to(endpoint); if (fd < 0) _exit(95); pause_ms(1000); close(fd); _exit(0); }
    int fake = accept_for(listener, 2000); assert(fake >= 0);
    assert(sosix_darwin_broker_observe_peer(&job, fake) == EACCES); close(fake);
    int status; assert(waitpid(impostor, &status, 0) == impostor); assert(status == 0);
    puts("same_uid_same_image_unrelated_peer: rejected");
    /* Execute a different image on the retained peer_observed connection. */
    byte = 'X'; assert(write(peer, &byte, 1) == 1);
    int changed = 0;
    for (int i = 0; i < 100; ++i) {
        if (sosix_darwin_broker_peer_identity(peer, job.peer_pid, (uint32_t)job.peer_identity.pid_version, &token, &identity)) { changed = 1; break; }
        pause_ms(10);
    }
    assert(changed); assert(sosix_darwin_broker_observe_peer(&job, peer) != 0);
    puts("post_exec_socket_token: rejected");
    close(peer); remove_job(&job); assert(job.peer_observed);
    puts("asynchronous_registration_removal: no_reap_claim");
    replace_registration(&job, 0);
    int rebound = accept_for(listener, 2000); assert(rebound >= 0);
    assert(sosix_darwin_broker_observe_peer(&job, rebound) == ESTALE);
    close(rebound); remove_job(&job); unlink(marker);
    puts("same_label_recreated_job: rejected");
    /* Replace the socket pathname with an attacker-owned listener. The helper
     * may connect, but must send no protocol byte to that process. */
    char rogue_endpoint[104]; assert(snprintf(rogue_endpoint, sizeof(rogue_endpoint), "%s/rogue", argv[2]) < (int)sizeof(rogue_endpoint));
    int ready[2]; assert(pipe(ready) == 0);
    pid_t rogue = fork(); assert(rogue >= 0);
    if (!rogue) {
        close(ready[0]); close(listener);
        int server = socket(AF_UNIX, SOCK_STREAM, 0); assert(server >= 0);
        struct sockaddr_un rogue_address = {.sun_family = AF_UNIX}; strcpy(rogue_address.sun_path, rogue_endpoint);
        assert(bind(server, (struct sockaddr *)&rogue_address, sizeof(rogue_address)) == 0);
        assert(listen(server, 1) == 0); assert(write(ready[1], "R", 1) == 1); close(ready[1]);
        int victim = accept_for(server, 3000); assert(victim >= 0);
        char leaked; assert(read_byte(victim, &leaked) == 0);
        close(victim); close(server); _exit(0);
    }
    close(ready[1]); assert(read_byte(ready[0], &byte) == 1 && byte == 'R'); close(ready[0]);
    SosixDarwinBrokerTransport rogue_job = {0};
    assert(sosix_darwin_broker_submit(&rogue_job, argv[0], rogue_endpoint, hash) == 0);
    assert(waitpid(rogue, &status, 0) == rogue && status == 0); remove_job(&rogue_job);
    unlink(rogue_endpoint);
    puts("same_uid_socket_path_substitution: no_protocol_bytes");
    /* A configuration takeover BEFORE the first observation cannot be
     * distinguished by GetJob: it omits the injected EnvironmentVariables.
     * Current PID/code observation is deliberately NOT admission authority. */
    SosixDarwinBrokerTransport pending = {0};
    assert(sosix_darwin_broker_submit(&pending, argv[0], endpoint, hash) == 0);
    remove_job(&pending);
    int abandoned;
    while ((abandoned = accept_for(listener, 0)) >= 0) close(abandoned);
    replace_registration(&pending, 1);
    int takeover = accept_for(listener, 2000); assert(takeover >= 0);
    launch_data_t hidden = sosix_darwin_broker_query(LAUNCH_KEY_GETJOB, pending.label);
    assert(hidden && launch_data_get_type(hidden) == LAUNCH_DATA_DICTIONARY);
    assert(!launch_data_dict_lookup(hidden, "EnvironmentVariables")); launch_data_free(hidden);
    assert(sosix_darwin_broker_observe_peer(&pending, takeover) == 0);
    assert(read_byte(takeover, &byte) == 1 && byte == 'E');
    close(takeover); remove_job(&pending); unlink(marker);
    puts("preauthentication_environment_takeover: observation_cannot_attest_admission");
    /* Negative control: no wrong-code process may even connect. */
    job = (SosixDarwinBrokerTransport){0};
    assert(sosix_darwin_broker_submit(&job, argv[0], endpoint, wrong) == 0);
    assert(accept_for(listener, 1200) < 0); assert(access(marker, F_OK) != 0); remove_job(&job);
    puts("wrong_spawn_cdhash: rejected_before_constructor");
    /* RED control: the substituted executable is healthy and enters when the
     * kernel launch constraint is omitted. */
    pid_t unbound = fork(); assert(unbound >= 0);
    if (!unbound) {
        char *args[] = {argv[3], SOSIX_DARWIN_BROKER_MODE, endpoint,
                       job.controller_pid, job.controller_version, NULL};
        execv(args[0], args); _exit(96);
    }
    int unbound_peer = accept_for(listener, 2000); assert(unbound_peer >= 0);
    assert(read_byte(unbound_peer, &byte) == 1 && byte == 'A'); close(unbound_peer);
    assert(waitpid(unbound, &status, 0) == unbound && status == 0);
    assert(access(marker, F_OK) == 0); unlink(marker);
    puts("unbound_replacement_control: enters_constructor");
    /* Replace the launch pathname after the expected hash was acquired. */
    assert(rename(argv[3], argv[0]) == 0);
    job = (SosixDarwinBrokerTransport){0};
    assert(sosix_darwin_broker_submit(&job, argv[0], endpoint, hash) == 0);
    assert(accept_for(listener, 1200) < 0); assert(access(marker, F_OK) != 0); remove_job(&job);
    puts("same_path_replacement: rejected_before_constructor");
    close(listener); unlink(endpoint);
    puts("original_job_admission_authority: unavailable");
    puts("generic_v4_capability: not_claimed");
    puts("darwin_broker_transport: pass");
    return 0;
}
