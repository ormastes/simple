/* Deterministic policy fixture; no process privileges or real sysctl calls. */
#include "macos-observer-denial-policy.h"
#include <assert.h>
#include <stddef.h>

struct fixture {
    const enum observer_denial_state *states;
    size_t count;
    size_t next;
    unsigned int waits;
};

static enum observer_denial_state next_state(void *opaque) {
    struct fixture *f = opaque;
    assert(f->next < f->count);
    return f->states[f->next++];
}

static void count_wait(void *opaque, unsigned int retry) {
    struct fixture *f = opaque;
    assert(retry == f->waits + 1);
    ++f->waits;
}

static void check(const enum observer_denial_state *states, size_t count,
                  int expected_gone, size_t expected_probes,
                  unsigned int expected_waits) {
    struct fixture f = { states, count, 0, 0 };
    int gone = observer_denial_proves_gone(next_state, count_wait, &f);
    assert(gone == expected_gone);
    assert(f.next == expected_probes);
    assert(f.waits == expected_waits);
}

int main(void) {
    const enum observer_denial_state exits_after_live[] = {
        OBSERVER_DENIAL_EXPECTED_LIVE, OBSERVER_DENIAL_GONE
    };
    const enum observer_denial_state zombie_after_live[] = {
        OBSERVER_DENIAL_EXPECTED_LIVE, OBSERVER_DENIAL_EXPECTED_ZOMBIE
    };
    const enum observer_denial_state persistent_live[] = {
        OBSERVER_DENIAL_EXPECTED_LIVE, OBSERVER_DENIAL_EXPECTED_LIVE,
        OBSERVER_DENIAL_EXPECTED_LIVE
    };
    const enum observer_denial_state immediate_reuse[] = {
        OBSERVER_DENIAL_REUSED_PID
    };
    const enum observer_denial_state unknown[] = { OBSERVER_DENIAL_UNKNOWN };
    const enum observer_denial_state immediate_gone[] = { OBSERVER_DENIAL_GONE };
    const enum observer_denial_state immediate_zombie[] = { OBSERVER_DENIAL_EXPECTED_ZOMBIE };

    check(exits_after_live, 2, 1, 2, 1);
    check(zombie_after_live, 2, 1, 2, 1);
    check(persistent_live, 3, 0, 3, 2);
    check(immediate_reuse, 1, 0, 1, 0);
    check(unknown, 1, 0, 1, 0);
    check(immediate_gone, 1, 1, 1, 0);
    check(immediate_zombie, 1, 1, 1, 0);
    return 0;
}
