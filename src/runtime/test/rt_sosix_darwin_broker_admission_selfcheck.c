#include "../runtime_sosix_darwin_broker_admission_private.h"
#include <assert.h>
#include <sys/stat.h>

static int accept_for(int fd, int ms) {
    struct pollfd p = {fd, POLLIN, 0};
    int n; do n = poll(&p, 1, ms); while (n < 0 && errno == EINTR);
    return n == 1 && (p.revents & POLLIN) ? accept(fd, NULL, NULL) : -1;
}
static void wait_clean(pid_t pid) {
    int status; while (waitpid(pid, &status, 0) < 0) assert(errno == EINTR);
    assert(WIFEXITED(status) && WEXITSTATUS(status) == 0);
}
int main(int argc, char **argv) {
    assert(argc == 5);
    int source = open(argv[1], O_RDONLY); assert(source >= 0);
    unsigned char digest[32]; assert(!sosix_darwin_image_hash(source, digest));
    SosixDarwinImage image; assert(!sosix_darwin_image_create_bound(source, digest, &image)); close(source);
    char endpoint[104]; assert(snprintf(endpoint, sizeof(endpoint), "%s/socket", argv[2]) < (int)sizeof(endpoint));
    char entered[PATH_MAX]; snprintf(entered, sizeof(entered), "%s.entered", endpoint);
    int listener = socket(AF_UNIX, SOCK_STREAM, 0); assert(listener >= 0);
    struct sockaddr_un address = {.sun_family = AF_UNIX}; strcpy(address.sun_path, endpoint);
    assert(!bind(listener, (struct sockaddr *)&address, sizeof(address))); assert(!listen(listener, 8));
    /* This file descriptor and all hostile variables must disappear BEFORE
     * the helper's constructor. The production helper refuses inherited env. */
    int leaked = open(argv[3], O_WRONLY | O_CREAT | O_TRUNC, 0600); assert(leaked >= 0);
    assert(!setenv("SOSIX_BROKER_ADVERSARIAL", "injected", 1));
    assert(!setenv("DYLD_INSERT_LIBRARIES", argv[4], 1));
    assert(!setenv("MallocStackLoggingDirectory", argv[2], 1));
    char injected[PATH_MAX]; snprintf(injected, sizeof(injected), "%s/injected", argv[2]);
    assert(!setenv("SOSIX_INJECTION_MARKER", injected, 1));
    SosixDarwinBrokerAdmission owner = {0};
    assert(!sosix_darwin_broker_spawn_closed(&image, image.generation, endpoint, &owner));
    assert(sosix_darwin_broker_spawn_closed(&image, image.generation, endpoint, &owner) == EALREADY);
    int peer = accept_for(listener, 3000); assert(peer >= 0);
    /* Unrelated same-UID peers cannot receive an admission byte. */
    pid_t impostor = fork(); assert(impostor >= 0);
    if (!impostor) {
        close(peer); close(listener);
        int fd = socket(AF_UNIX, SOCK_STREAM, 0); assert(fd >= 0);
        assert(!connect(fd, (struct sockaddr *)&address, sizeof(address)));
        struct pollfd p = {fd, POLLIN, 0}; assert(poll(&p, 1, 2000) == 1);
        char byte; assert(read(fd, &byte, 1) == 0); close(fd); _exit(0);
    }
    int fake = accept_for(listener, 2000); assert(fake >= 0);
    assert(sosix_darwin_broker_admit(&owner, fake, 1000) == EACCES); close(fake); wait_clean(impostor);
    assert(!owner.admitted); puts("direct_child_impostor: rejected_before_admission");
    SosixDarwinBrokerAdmission wrong = owner; wrong.cdhash[0] ^= 1;
    assert(sosix_darwin_broker_admit(&wrong, peer, 1000) == EACCES);
    wrong = owner; wrong.identity.pid_version++;
    assert(sosix_darwin_broker_admit(&wrong, peer, 1000) == EACCES);
    assert(!sosix_darwin_broker_admit(&owner, peer, 1000)); assert(owner.admitted); assert(access(injected, F_OK) != 0);
    assert(!access(entered, F_OK)); assert(!unlink(entered));
    assert(sosix_darwin_broker_admit(&owner, peer, 1000) == EALREADY);
    char byte = 'P'; assert(write(peer, &byte, 1) == 1);
    assert(!sosix_darwin_broker_read_byte(peer, &byte, 1000) && byte == 'P');
    puts("canonical_helper_empty_environment_and_closed_descriptors: admitted");
    puts("direct_child_wrong_hash_and_incarnation: rejected");
    assert(!sosix_darwin_broker_admission_close(&owner, 1000)); close(peer);
    assert(owner.reaped && !owner.admitted); close(leaked);
    assert(sosix_darwin_broker_admission_close(&owner, 1000) == EALREADY);
    puts("direct_child_shutdown: bounded_reap_receipt");
    puts("dyld_injected_constructor: excluded_before_main");
    /* Same-UID pathname replacement gives a socket to a different process,
     * which must see EOF and no readiness/admission bytes. */
    char rogue_path[104]; assert(snprintf(rogue_path, sizeof(rogue_path), "%s/rogue", argv[2]) < (int)sizeof(rogue_path));
    int ready[2]; assert(!pipe(ready));
    pid_t rogue = fork(); assert(rogue >= 0);
    if (!rogue) {
        close(ready[0]); close(listener);
        int server = socket(AF_UNIX, SOCK_STREAM, 0); assert(server >= 0);
        struct sockaddr_un rogue_address = {.sun_family = AF_UNIX}; strcpy(rogue_address.sun_path, rogue_path);
        assert(!bind(server, (struct sockaddr *)&rogue_address, sizeof(rogue_address))); assert(!listen(server, 1));
        assert(write(ready[1], "R", 1) == 1); close(ready[1]);
        int victim = accept_for(server, 3000); assert(victim >= 0);
        char leaked_byte; assert(sosix_darwin_broker_read_byte(victim, &leaked_byte, 1000) == EPIPE);
        close(victim); close(server); _exit(0);
    }
    close(ready[1]); assert(read(ready[0], &byte, 1) == 1); close(ready[0]);
    SosixDarwinBrokerAdmission rogue_owner = {0};
    assert(!sosix_darwin_broker_spawn_closed(&image, image.generation, rogue_path, &rogue_owner));
    wait_clean(rogue); assert(!sosix_darwin_broker_admission_close(&rogue_owner, 1000)); unlink(rogue_path);
    puts("direct_child_socket_replacement: no_protocol_bytes");
    SosixDarwinBrokerAdmission lost = {.pid = getpid()};
    assert(sosix_darwin_broker_admission_close(&lost, 1000) == ECHILD);
    puts("lost_child_authority: no_signal");
    /* The helper remains live and closed while waiting for admission. A
     * silent peer must time out; cancellation must reap even a stopped child. */
    SosixDarwinBrokerAdmission pending = {0};
    assert(!sosix_darwin_broker_spawn_closed(&image, image.generation, endpoint, &pending));
    int waiting = accept_for(listener, 2000); assert(waiting >= 0);
    assert(!sosix_darwin_broker_read_byte(waiting, &byte, 1000) && byte == 'R');
    assert(sosix_darwin_broker_read_byte(waiting, &byte, 30) == ETIMEDOUT);
    assert(!pending.admitted); assert(!kill(pending.pid, SIGSTOP));
    assert(!sosix_darwin_broker_admission_close(&pending, 1000)); assert(pending.reaped);
    close(waiting); assert(!unlink(entered));
    puts("closed_gate_silence_and_stopped_child: timeout_and_reap");
    /* Saturate an attacker's endpoint. A closed helper uses the same bounded
     * nonblocking connect primitive and never waits indefinitely in connect. */
    int crowded = socket(AF_UNIX, SOCK_STREAM, 0); assert(crowded >= 0);
    struct sockaddr_un crowded_address = {.sun_family = AF_UNIX};
    assert(snprintf(crowded_address.sun_path, sizeof(crowded_address.sun_path), "%s/crowded", argv[2]) < (int)sizeof(crowded_address.sun_path));
    assert(!bind(crowded, (struct sockaddr *)&crowded_address, sizeof(crowded_address))); assert(!listen(crowded, 1));
    int clients[8], refused = 0, used = 0;
    int64_t began = sosix_darwin_coalition_now_ns();
    for (; used < 8; ++used) {
        clients[used] = socket(AF_UNIX, SOCK_STREAM, 0); assert(clients[used] >= 0);
        int result = sosix_darwin_broker_connect(clients[used], &crowded_address, 30);
        if (result) { refused = 1; ++used; break; }
    }
    assert(refused); assert(sosix_darwin_coalition_now_ns() - began < 1000000000);
    for (int i = 0; i < used; ++i) close(clients[i]);
    close(crowded); unlink(crowded_address.sun_path);
    puts("saturated_endpoint_connect: bounded");
    /* A bound image's CDHash, not pathname observation, gates constructors. */
    unsigned char saved[20]; memcpy(saved, image.cdhash, 20); image.cdhash[0] ^= 1;
    SosixDarwinBrokerAdmission denied = {0};
    int e = sosix_darwin_broker_spawn_closed(&image, image.generation, endpoint, &denied);
    if (!e) {
        /* Never kill first: that could hide a missing launch constraint by
         * racing the valid helper's constructor. Require natural denial. */
        int status = 0; pid_t exited = 0;
        int64_t deadline = sosix_darwin_coalition_now_ns() + 1000000000;
        do {
            exited = waitpid(denied.pid, &status, WNOHANG);
            if (exited < 0) assert(errno == EINTR);
            if (exited == denied.pid) break;
            struct timespec delay = {0, 1000000}; nanosleep(&delay, NULL);
        } while (sosix_darwin_coalition_now_ns() < deadline);
        assert(exited == denied.pid);
        assert(!WIFEXITED(status) || WEXITSTATUS(status) != 0);
        denied.reaped = 1;
    }
    assert(accept_for(listener, 0) < 0); assert(access(entered, F_OK) != 0); memcpy(image.cdhash, saved, 20);
    puts("direct_child_wrong_spawn_hash: rejected_before_constructor");
    /* A caller cannot upgrade the cooperative image route to admission. */
    image.kernel_bound = 0;
    denied = (SosixDarwinBrokerAdmission){0};
    assert(sosix_darwin_broker_spawn_closed(&image, image.generation, endpoint, &denied) == ENOTSUP);
    image.kernel_bound = 1;
    assert(!sosix_darwin_image_close(&image, image.generation));
    close(listener); unlink(endpoint);
    puts("unbound_image: admission_rejected");
    puts("disjoint_coalition_authority: unavailable");
    puts("generic_v4_capability: not_claimed");
    puts("darwin_broker_admission: pass");
}
