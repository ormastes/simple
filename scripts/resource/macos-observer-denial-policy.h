/* Permission-error race policy shared by the Darwin observer and its fixture. */
#ifndef MACOS_OBSERVER_DENIAL_POLICY_H
#define MACOS_OBSERVER_DENIAL_POLICY_H

enum observer_denial_state {
    OBSERVER_DENIAL_GONE,
    OBSERVER_DENIAL_EXPECTED_ZOMBIE,
    OBSERVER_DENIAL_EXPECTED_LIVE,
    OBSERVER_DENIAL_REUSED_PID,
    OBSERVER_DENIAL_UNKNOWN
};

enum { OBSERVER_DENIAL_MAX_PROBES = 3 };

typedef enum observer_denial_state (*observer_denial_probe)(void *context);
typedef void (*observer_denial_wait)(void *context, unsigned int retry);

/* A live same-identity result is provisional: a short-lived process may exit
 * between the denied detail syscall and the independent kernel proof. Retry
 * that state a bounded number of times. Every other state fails closed unless
 * it is authoritative absence or the expected identity in zombie state. */
static int observer_denial_proves_gone(observer_denial_probe probe,
                                       observer_denial_wait wait,
                                       void *context) {
    for (unsigned int attempt = 0; attempt < OBSERVER_DENIAL_MAX_PROBES; ++attempt) {
        enum observer_denial_state state = probe(context);
        if (state == OBSERVER_DENIAL_GONE ||
            state == OBSERVER_DENIAL_EXPECTED_ZOMBIE) return 1;
        if (state != OBSERVER_DENIAL_EXPECTED_LIVE) return 0;
        if (attempt + 1 < OBSERVER_DENIAL_MAX_PROBES) wait(context, attempt + 1);
    }
    return 0;
}

#endif
