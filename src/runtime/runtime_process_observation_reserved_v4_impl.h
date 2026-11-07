/* Included only by the canonical native process owner, after its V4 helpers.
 * No PID authority escapes this boundary. All returned tuple pointers may be
 * NULL: reservation authority survives failed result allocation/decoding. */
static Pov4Reservation* pov4_reservation_acquire(int64_t token) {
    if (token <= 0) { errno = ESTALE; return NULL; }
    pthread_mutex_lock(&pov4_reservations_lock);
    Pov4Reservation* found = NULL;
    errno = ESTALE;
    for (int i = 0; i < POV4_SLOTS; ++i) {
        Pov4Reservation* r = &pov4_reservations[i];
        if (r->token != token) continue;
        if (r->busy) errno = EBUSY;
        else { r->busy = 1; found = r; }
        break;
    }
    pthread_mutex_unlock(&pov4_reservations_lock);
    return found;
}

static void pov4_reservation_release_busy(Pov4Reservation* r) {
    pthread_mutex_lock(&pov4_reservations_lock);
    r->busy = 0;
    pthread_mutex_unlock(&pov4_reservations_lock);
}

static Pov4Slot* pov4_reservation_owner(Pov4Reservation* r) {
    if (r->owner_index >= POV4_SLOTS) return NULL;
    Pov4Slot* owner = &pov4_slots[r->owner_index];
    if (!owner->active || owner->reservation_token != r->token) return NULL;
    return owner;
}

int64_t rt_process_observation_v4_reserve_value(void) {
    pthread_mutex_lock(&pov4_reservations_lock);
    int64_t result = -EAGAIN;
    for (int i = 0; i < POV4_SLOTS; ++i) {
        Pov4Reservation* r = &pov4_reservations[i];
        if (r->token) continue;
        if (pov4_reservation_sequence >= INT64_MAX) { result = -EOVERFLOW; break; }
        memset(r, 0, sizeof(*r));
        r->token = (int64_t)++pov4_reservation_sequence;
        r->state = 1;
        r->owner_index = UINT32_MAX;
        result = r->token;
        break;
    }
    pthread_mutex_unlock(&pov4_reservations_lock);
    return result;
}

int64_t rt_process_observation_v4_reserved_state_value(int64_t token) {
    Pov4Reservation* r = pov4_reservation_acquire(token);
    if (!r) return -errno;
    int64_t result = r->state;
    pov4_reservation_release_busy(r);
    return result;
}

static int64_t pov4_reserved_start_admitted_impl(
    int64_t token, int64_t executable, int64_t cwd, SplArray* binding,
    int deadline_required, int64_t expires_at_unix_ms) {
    Pov4Reservation* r = pov4_reservation_acquire(token);
    if (!r) return -errno;
    if (r->state != 1) { pov4_reservation_release_busy(r); return -EALREADY; }
    /* Attempt is irrevocable even on invalid input/allocation failure. No
     * competing/repeated caller can launch another child with this token. */
    r->state = 2;
    r->executable_pin = executable;
    r->cwd_pin = cwd;
    r->submission_expires_unix_ms = deadline_required ? expires_at_unix_ms : 0;
    int admission_error = deadline_required && expires_at_unix_ms<=0 ? EINVAL :
        pov5_submission_admission_check(r->submission_expires_unix_ms);
    if (admission_error) {
        r->submission_admission_error = admission_error;
        r->state = 3;
        pov4_reservation_release_busy(r);
        return -admission_error;
    }
    Pov4Request request;
    if (!pov4_request_from_value(binding, &request)) {
        r->state = 3;
        pov4_reservation_release_busy(r);
        return 0;
    }
    memcpy(r->request_digest, request.request_digest, 32);
    pov4_request_free(&request);
    SplArray* initial = pov4_start_pinned_impl(executable, cwd, binding,
                                               NULL, NULL, 0, r);
    /* This internal tuple is not authority. A NULL or malformed tuple cannot
     * lose the slot already bound before spawn; callers observe by reservation. */
    if (initial) pov4_tuple4_free(initial);
    int64_t result = r->state == 4 ? 1 :
        (r->submission_admission_error ? -r->submission_admission_error : 0);
    if (r->state != 4) { r->state = 3; r->owner_index = UINT32_MAX; }
    pov4_reservation_release_busy(r);
    return result;
}

int64_t rt_process_observation_v4_reserved_start_pinned_value(
    int64_t token, int64_t executable, int64_t cwd, SplArray* binding) {
    return pov4_reserved_start_admitted_impl(token,executable,cwd,binding,0,0);
}

int64_t rt_process_observation_v5_reserved_start_admitted_value(
    int64_t token, int64_t executable, int64_t cwd, SplArray* binding,
    int64_t expires_at_unix_ms) {
    return pov4_reserved_start_admitted_impl(token,executable,cwd,binding,1,expires_at_unix_ms);
}

SplArray* rt_process_observation_v4_reserved_observe_value(
    int64_t token, int64_t wait_ns, int64_t retire) {
    Pov4Reservation* r = pov4_reservation_acquire(token);
    if (!r) return NULL;
    Pov4Slot* owner = pov4_reservation_owner(r);
    SplArray* result = NULL;
    if ((r->state == 4 || r->state == 5) && owner) {
        if (!owner->frozen) {
            int terminal = 0;
            SplArray* progress = pov4_drive(owner, wait_ns, retire != 0, 0, &terminal);
            if (terminal) {
                if (progress) pov4_tuple4_free(progress);
                result = pov4_freeze_terminal(owner);
            } else result = progress;
        } else {
            owner->words[POV4_STDOUT_PAYLOAD_LENGTH] = (int64_t)owner->stdout_count;
            owner->words[POV4_STDERR_PAYLOAD_LENGTH] = (int64_t)owner->stderr_count;
            result = pov4_tuple4(owner->stdout_bytes, owner->stdout_count,
                owner->stderr_bytes, owner->stderr_count, owner->frozen_digest,
                POV4_DIGEST_BYTES, owner->words);
        }
    }
#ifdef RT_PROCESS_OBSERVATION_V4_TESTING
    if (result && pov4_reservation_test_corrupt_observe > 0) {
        --pov4_reservation_test_corrupt_observe;
        SplArray* words = (SplArray*)(uintptr_t)rt_array_get(result, 3);
        rt_array_set(words, POV4_VERSION, rt_value_int(-1));
    }
#endif
    pov4_reservation_release_busy(r);
    return result;
}

SplArray* rt_process_observation_v4_reserved_ack_value(int64_t token, SplArray* digest_value) {
    Pov4Reservation* r = pov4_reservation_acquire(token);
    if (!r) return NULL;
    Pov4Slot* owner = pov4_reservation_owner(r);
    uint8_t digest[POV4_DIGEST_BYTES];
    SplArray* result = NULL;
    if ((r->state == 4 || r->state == 5) && owner && owner->frozen &&
        rt_array_bytes_copy_checked((int64_t)(uintptr_t)digest_value,
                                     digest, sizeof(digest)) == (int64_t)sizeof(digest) &&
        memcmp(digest, owner->frozen_digest, sizeof(digest)) == 0) {
        int64_t ack[POV4_WORDS];
        memcpy(ack, owner->words, sizeof(ack));
        ack[POV4_PACKET_KIND] = owner->cleanup_only ? POV4_KIND_CLEANUP_ACK : POV4_KIND_ACK;
        ack[POV4_PHASE] = POV4_PHASE_ACK;
        ack[POV4_STDOUT_PAYLOAD_LENGTH] = 0;
        ack[POV4_STDERR_PAYLOAD_LENGTH] = 0;
        ack[POV4_BINDING_LENGTH] = POV4_DIGEST_BYTES;
        result = pov4_tuple4(NULL, 0, NULL, 0, owner->frozen_digest, POV4_DIGEST_BYTES, ack);
        /* Idempotent even if result allocation or caller decoding fails. */
        r->state = 5;
    }
#ifdef RT_PROCESS_OBSERVATION_V4_TESTING
    if (result && pov4_reservation_test_corrupt_ack > 0) {
        --pov4_reservation_test_corrupt_ack;
        SplArray* words = (SplArray*)(uintptr_t)rt_array_get(result, 3);
        rt_array_set(words, POV4_VERSION, rt_value_int(-1));
    }
#endif
    pov4_reservation_release_busy(r);
    return result;
}

int64_t rt_process_observation_v4_reserved_confirm_release_value(int64_t token) {
    Pov4Reservation* r = pov4_reservation_acquire(token);
    if (!r) return -errno;
    if (r->state != 1 && r->state != 3 && r->state != 5) {
        pov4_reservation_release_busy(r); return -EBUSY;
    }
    if (r->state == 5) {
        Pov4Slot* owner = pov4_reservation_owner(r);
        if (!owner || !owner->frozen) {
            pov4_reservation_release_busy(r); return -EPROTO;
        }
        pthread_mutex_lock(&pov4_slots_lock);
        RT_OWNED_HOST_FREE(owner->stdout_bytes);
        RT_OWNED_HOST_FREE(owner->stderr_bytes);
        memset(owner, 0, sizeof(*owner));
        pthread_mutex_unlock(&pov4_slots_lock);
    }
    pthread_mutex_lock(&pov4_reservations_lock);
    memset(r, 0, sizeof(*r));
    pthread_mutex_unlock(&pov4_reservations_lock);
    return 1;
}

int64_t rt_process_observation_v4_reserved_matches_value(int64_t token,
    int64_t rh, int64_t rl, int64_t th, int64_t tl) {
    Pov4Reservation* r = pov4_reservation_acquire(token);
    if (!r) return -errno;
    Pov4Slot* owner = pov4_reservation_owner(r);
    int64_t matches = owner && rh > 0 && rl > 0 && th > 0 && tl > 0 &&
        owner->request_high == (uint64_t)rh && owner->request_low == (uint64_t)rl &&
        owner->ticket_high == (uint64_t)th && owner->ticket_low == (uint64_t)tl;
    pov4_reservation_release_busy(r);
    return matches;
}
