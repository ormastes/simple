/* Experimental bound launch attempts and kernel stream peer observations.
 * GetJob omits launch environment/constraints. A same-UID actor can replace a
 * label BEFORE first observation; exact code/PID does NOT attest submission
 * provenance. observe_peer grants NO admission or owned-coalition authority.
 * No V4 capability: callers still owe closed admission, dependency policy,
 * descendant confinement, resource enforcement, and a reap receipt.
 * The CDHash is caller-trusted (e.g. from the bound image owner), NEVER derived
 * from the launch pathname here. Keep the image alive through submission.
 * The trusted helper must also enforce hardening/dependency policy, never pass
 * its socket to another process, and never exec between authentication and use.
 * Single-owner state; serialize calls. No workload admission through this API.
 */
#ifndef RUNTIME_SOSIX_DARWIN_BROKER_TRANSPORT_PRIVATE_H
#define RUNTIME_SOSIX_DARWIN_BROKER_TRANSPORT_PRIVATE_H
#ifdef __APPLE__
#include "runtime_sosix_darwin_coalition_private.h"
#include <launch.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <sys/sysctl.h>
#include <stdio.h>
#include <limits.h>

#define SOSIX_DARWIN_BROKER_MODE "--sosix-darwin-broker"
typedef struct {
    char label[96], program[PATH_MAX], endpoint[104], controller_pid[24], controller_version[24];
    unsigned char cdhash[20];
    int submitted, peer_observed; /* submitted includes an uncertain reply */
    pid_t peer_pid;
    SosixDarwinProcessIdentity peer_identity;
    audit_token_t peer_token;
} SosixDarwinBrokerTransport;

static const char *sosix_darwin_broker_argument(const SosixDarwinBrokerTransport *job, size_t i) {
    const char *args[] = {job->program, SOSIX_DARWIN_BROKER_MODE, job->endpoint,
                         job->controller_pid, job->controller_version};
    return i < 5 ? args[i] : NULL;
}
static int sosix_darwin_broker_put(launch_data_t dictionary, const char *key, launch_data_t value) {
    if (!value) return ENOMEM;
    if (launch_data_dict_insert(dictionary, value, key)) return 0;
    launch_data_free(value); return ENOMEM;
}
static int sosix_darwin_broker_reply_error(launch_data_t reply) {
    if (!reply) return errno ? errno : EIO;
    return launch_data_get_type(reply) == LAUNCH_DATA_ERRNO ? launch_data_get_errno(reply) : EPROTO;
}
static launch_data_t sosix_darwin_broker_query(const char *operation, const char *label) {
    launch_data_t message = launch_data_alloc(LAUNCH_DATA_DICTIONARY);
    if (!message) { errno = ENOMEM; return NULL; }
    int e = sosix_darwin_broker_put(message, operation, launch_data_new_string(label));
    launch_data_t reply = e ? NULL : launch_msg(message);
    int saved = e ? e : errno; launch_data_free(message); errno = saved;
    return reply;
}

static int sosix_darwin_broker_submit(SosixDarwinBrokerTransport *job,
        const char *program, const char *endpoint, const unsigned char cdhash[20]) {
    if (!job || !program || !endpoint || !cdhash || program[0] != '/' || endpoint[0] != '/') return EINVAL;
    if (job->submitted) return EALREADY;
    if (strlen(program) >= sizeof(job->program) || strlen(endpoint) >= sizeof(job->endpoint)) return ENAMETOOLONG;
    int allowed = 0; size_t allowed_size = sizeof(allowed);
    if (sysctlbyname("security.mac.amfi.launch_constraints_3rd_party_allowed", &allowed,
                    &allowed_size, NULL, 0) || allowed_size != sizeof(allowed) || allowed != 1) return ENOTSUP;
    SosixDarwinProcessIdentity controller;
    int e = sosix_darwin_coalition_identity(getpid(), &controller, 0);
    if (e) return e;
    memset(job, 0, sizeof(*job));
    unsigned char nonce[16]; arc4random_buf(nonce, sizeof(nonce));
    strcpy(job->label, "org.simple.sosix.broker.");
    size_t prefix = strlen(job->label);
    for (size_t i = 0; i < sizeof(nonce); ++i) snprintf(job->label + prefix + 2*i, 3, "%02x", nonce[i]);
    strcpy(job->program, program); strcpy(job->endpoint, endpoint); memcpy(job->cdhash, cdhash, 20);
    snprintf(job->controller_pid, sizeof(job->controller_pid), "%d", getpid());
    snprintf(job->controller_version, sizeof(job->controller_version), "%u", (unsigned)controller.pid_version);
    launch_data_t message = launch_data_alloc(LAUNCH_DATA_DICTIONARY);
    launch_data_t description = launch_data_alloc(LAUNCH_DATA_DICTIONARY);
    launch_data_t arguments = launch_data_alloc(LAUNCH_DATA_ARRAY);
    launch_data_t constraint = launch_data_alloc(LAUNCH_DATA_DICTIONARY);
    if (!message || !description || !arguments || !constraint) { e = ENOMEM; goto done; }
    for (size_t i = 0; i < 5; ++i) {
        launch_data_t value = launch_data_new_string(sosix_darwin_broker_argument(job, i));
        if (!value) { e = ENOMEM; goto done; }
        if (!launch_data_array_set_index(arguments, value, i)) { launch_data_free(value); e = ENOMEM; goto done; }
    }
    if ((e = sosix_darwin_broker_put(description, LAUNCH_JOBKEY_LABEL, launch_data_new_string(job->label))) ||
        (e = sosix_darwin_broker_put(description, "RunAtLoad", launch_data_new_bool(1))) ||
        (e = sosix_darwin_broker_put(description, "LaunchOnlyOnce", launch_data_new_bool(1))) ||
        (e = sosix_darwin_broker_put(description, "KeepAlive", launch_data_new_bool(0))) ||
        (e = sosix_darwin_broker_put(constraint, "cdhash", launch_data_new_opaque(cdhash, 20)))) goto done;
    e = sosix_darwin_broker_put(description, LAUNCH_JOBKEY_PROGRAMARGUMENTS, arguments); arguments = NULL;
    if (e) goto done;
    e = sosix_darwin_broker_put(description, "SpawnConstraint", constraint); constraint = NULL;
    if (e) goto done;
    e = sosix_darwin_broker_put(message, LAUNCH_KEY_SUBMITJOB, description); description = NULL;
    if (e) goto done;
    job->submitted = 1; /* A lost reply must retain the label for housekeeping. */
    launch_data_t reply = launch_msg(message);
    e = sosix_darwin_broker_reply_error(reply);
    if (reply) launch_data_free(reply);
done:
    if (constraint) launch_data_free(constraint);
    if (arguments) launch_data_free(arguments);
    if (description) launch_data_free(description);
    if (message) launch_data_free(message);
    return e;
}

/* LOCAL_PEERTOKEN is kernel provenance, unlike a PID or token in a packet.
 * Reject stale post-exec tokens too. It does not confer exclusivity if a trusted
 * process deliberately transfers its socket; the broker must never do that. */
static int sosix_darwin_broker_peer_identity(int fd, pid_t expected_pid, uint32_t expected_version,
        audit_token_t *token, SosixDarwinProcessIdentity *identity) {
    if (fd < 0 || expected_pid <= 1 || !token || !identity) return EINVAL;
    int kind = 0; socklen_t length = sizeof(kind);
    if (getsockopt(fd, SOL_SOCKET, SO_TYPE, &kind, &length)) return errno;
    if (length != sizeof(kind) || kind != SOCK_STREAM) return EPROTOTYPE;
    length = sizeof(*token);
    if (getsockopt(fd, SOL_LOCAL, LOCAL_PEERTOKEN, token, &length)) return errno;
    if (length != sizeof(*token) || token->val[5] != (uint32_t)expected_pid ||
        token->val[7] != expected_version || token->val[1] != (uint32_t)geteuid()) return EACCES;
    int e = sosix_darwin_coalition_identity(expected_pid, identity, 0);
    if (!e && (uint32_t)identity->pid_version != expected_version) e = ESTALE;
    return e;
}
static int sosix_darwin_broker_peer_cdhash(audit_token_t *token, const unsigned char expected[20]) {
    if (!token || !expected || token->val[5] <= 1) return EINVAL;
    typedef int (*CodeStatusFn)(pid_t, unsigned int, void *, size_t, audit_token_t *);
    CodeStatusFn status = (CodeStatusFn)dlsym(RTLD_DEFAULT, "csops_audittoken");
    if (!status) return ENOTSUP;
    unsigned char actual[20];
    if (status((pid_t)token->val[5], 5 /* CS_OPS_CDHASH */, actual, sizeof(actual), token)) return errno ? errno : EIO;
    return memcmp(actual, expected, sizeof(actual)) ? EACCES : 0;
}

/* GetJob is discovery only and hides EnvironmentVariables/SpawnConstraint.
 * This observes current code and incarnation, NOT original-job provenance.
 * Even a successful first observation cannot authorize workload admission.
 * Check its program/argv and compare the socket kernel identity and code hash.
 * Once observed, pin the incarnation: a re-submitted label cannot rebind.
 * Re-observation detects some stale peers but never upgrades admission authority. */
static int sosix_darwin_broker_observe_peer(SosixDarwinBrokerTransport *job, int fd) {
    if (!job || !job->submitted || fd < 0) return EINVAL;
    launch_data_t reply = sosix_darwin_broker_query(LAUNCH_KEY_GETJOB, job->label);
    if (!reply) return errno ? errno : EIO;
    int e = EPROTO;
    pid_t pid = 0;
    if (launch_data_get_type(reply) != LAUNCH_DATA_DICTIONARY) {
        e = sosix_darwin_broker_reply_error(reply); if (!e) e = EPROTO; goto done;
    }
    launch_data_t args = launch_data_dict_lookup(reply, LAUNCH_JOBKEY_PROGRAMARGUMENTS);
    launch_data_t pid_value = launch_data_dict_lookup(reply, LAUNCH_JOBKEY_PID);
    launch_data_t program = launch_data_dict_lookup(reply, LAUNCH_JOBKEY_PROGRAM);
    if (!program || launch_data_get_type(program) != LAUNCH_DATA_STRING ||
        strcmp(launch_data_get_string(program), job->program)) { e = EACCES; goto done; }
    if (!args || launch_data_get_type(args) != LAUNCH_DATA_ARRAY || launch_data_array_get_count(args) != 5 ||
        !pid_value || launch_data_get_type(pid_value) != LAUNCH_DATA_INTEGER) goto done;
    long long raw_pid = launch_data_get_integer(pid_value);
    if (raw_pid <= 1 || raw_pid > INT_MAX) goto done;
    pid = (pid_t)raw_pid;
    for (size_t i = 0; i < 5; ++i) {
        launch_data_t value = launch_data_array_get_index(args, i);
        if (!value || launch_data_get_type(value) != LAUNCH_DATA_STRING ||
            strcmp(launch_data_get_string(value), sosix_darwin_broker_argument(job, i))) { e = EACCES; goto done; }
    }
    SosixDarwinProcessIdentity before, after; audit_token_t token;
    e = sosix_darwin_coalition_identity(pid, &before, 0);
    if (e) goto done;
    e = sosix_darwin_broker_peer_identity(fd, pid, (uint32_t)before.pid_version, &token, &after);
    if (!e && before.unique_id != after.unique_id) e = ESTALE;
    if (!e) e = sosix_darwin_broker_peer_cdhash(&token, job->cdhash);
    if (!e && job->peer_observed && (job->peer_pid != pid ||
        job->peer_identity.unique_id != after.unique_id ||
        job->peer_identity.pid_version != after.pid_version)) e = ESTALE;
    if (!e) {
        job->peer_pid = pid; job->peer_identity = after; job->peer_token = token; job->peer_observed = 1;
    }
done:
    launch_data_free(reply); return e;
}

/* Label-scoped housekeeping only, NEVER an owned kill/reap operation. A hostile
 * same-UID process can replace a launchd job; labels are not authority handles.
 * EINPROGRESS is propagated and submitted remains set until launchd says absent.
 * Observed peer identity stays pinned even after removal. Use guarded coalition lifecycle
 * separately; RemoveJob success does not prove descendants or zombies are gone. */
static int sosix_darwin_broker_remove_registration(SosixDarwinBrokerTransport *job) {
    if (!job || !job->submitted) return EINVAL;
    launch_data_t reply = sosix_darwin_broker_query(LAUNCH_KEY_REMOVEJOB, job->label);
    int e = sosix_darwin_broker_reply_error(reply);
    if (reply) launch_data_free(reply);
    if (e == ESRCH) job->submitted = 0;
    return e;
}
#endif
#endif
