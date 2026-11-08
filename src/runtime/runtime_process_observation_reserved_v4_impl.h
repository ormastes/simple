/* Included only by the canonical native process owner, after its V4 helpers.
 * No PID authority escapes this boundary. All returned tuple pointers may be
 * NULL: reservation authority survives failed result allocation/decoding. */
static int pov6_current_tid(void) {
#if defined(__linux__) && defined(SYS_gettid)
    long value=syscall(SYS_gettid);return value>0&&value<=INT_MAX?(int)value:0;
#else
    return 0;
#endif
}
static Pov4Reservation* pov4_reservation_acquire(int64_t token) {
    if(!pov6_reservation_origin())return NULL;
    if (token <= 0) { errno = ESTALE; return NULL; }
    pthread_mutex_lock(&pov4_reservations_lock);
    Pov4Reservation* found = NULL;
    errno = ESTALE;
    for (int i = 0; i < POV4_SLOTS; ++i) {
        Pov4Reservation* r = &pov4_reservations[i];
        if (r->token != token) continue;
        /* Existing short registry gate locates actual reservation metadata.
         * V6 thread admission precedes every core/per-child lock and ptrace. */
        if (r->busy) errno = EBUSY;
        else if(r->deferred_launch&&(r->submit_tid<=0||r->submit_tid!=pov6_current_tid()
#if defined(__linux__)
            ||r->submit_thread_stamp==0||r->submit_thread_stamp!=pov6_current_thread_stamp()
#endif
            ))errno=EPERM;
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
    if(!pov6_reservation_origin())return -errno;
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
    if(r->state==6){pov4_reservation_release_busy(r);errno=EBUSY;return NULL;}
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
    if(r->state==6){pov4_reservation_release_busy(r);errno=EBUSY;return NULL;}
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

/* Additive Linux V6. Progress scalars are NOT V4 observation statuses:
 * 0 actual no-child, 1 actual owned launch pending, 2 V4 observation available. */
#ifdef __linux__
enum { POV6_WAIT_STOP=1, POV6_OPTIONS=2, POV6_CONTINUE=3, POV6_WAIT_EXEC=4,
       POV6_KILL=5, POV6_WAIT_EXIT=6, POV6_KILL_CONTINUE=7, POV6_ERROR_READ=8,
       POV6_UNCERTAIN=9, POV6_DETACH=10 };
static void pov6_failure_locked(RtOwnedSlot* core,int error,int failure_class) {
    if(!core->launch_failure){core->launch_failure=error?error:EIO;core->launch_failure_class=failure_class;}
    core->runtime_error=core->launch_failure;
    if((core->launch_phase>=POV6_WAIT_STOP&&core->launch_phase<=POV6_WAIT_EXEC)||core->launch_phase==POV6_DETACH)
        core->launch_phase=core->reaped?POV6_ERROR_READ:POV6_KILL;
}
static void pov6_close_exec_locked(RtOwnedSlot* core) {
    int fd=core->launch_exec_fd;core->launch_exec_fd=-1;
    if(fd>=0&&close(fd)!=0&&!core->runtime_error)core->runtime_error=errno?errno:EIO;
}
static void pov6_reaped_locked(RtOwnedSlot* core,int status) {
    core->reaped=1;core->status=status;core->leader_waited_ns=owned_now_ns();
    if(core->leader_waited_ns<0)core->clock_failed=1;
    core->finished_ms=core->leader_waited_ns<0?-1:core->leader_waited_ns/1000000;
    owned_arm_unlimited_cleanup(core,core->leader_waited_ns,0);
    core->launch_phase=POV6_ERROR_READ;
}
/* One syscall progression, never a wait/reconcile/deadline loop. Trace-stop
 * events stay private to state 6 until detach or an actual terminal wait. */
static int pov6_step_locked(RtOwnedSlot* core,int retire) {
    if(core->launch_phase==POV6_UNCERTAIN)return -(core->launch_failure?core->launch_failure:EPROTO);
    int64_t now=owned_now_ns();
    if(now<0){core->clock_failed=1;pov6_failure_locked(core,EIO,RT_OWNED_EXEC_FAILURE_CLOCK_V4);}
    else if(retire&&!core->reaped){core->cancel_requested=1;pov6_failure_locked(core,ECANCELED,RT_OWNED_EXEC_FAILURE_PROVIDER_V4);}
    else if(!core->reaped&&now>=core->launch_confirm_deadline_ns){core->timed_out=1;pov6_failure_locked(core,ETIMEDOUT,RT_OWNED_EXEC_FAILURE_DEADLINE_V4);}
    int phase=core->launch_phase;
    if(phase==POV6_KILL) {
        core->kill_attempted=1;
        int rc;
#ifdef SYS_pidfd_send_signal
        if(core->pidfd<0) {
            core->launch_phase=POV6_UNCERTAIN;
            return -(core->launch_failure?core->launch_failure:ENOTSUP);
        }
        rc=(int)syscall(SYS_pidfd_send_signal,core->pidfd,SIGKILL,NULL,0);
#else
        core->launch_phase=POV6_UNCERTAIN;
        return -(core->launch_failure?core->launch_failure:ENOTSUP);
#endif
        if(rc==0)core->kill_sent=1;
        else if(errno==EINTR){core->eintr_retries=owned_add_sat(core->eintr_retries,1);return 1;}
        else if(errno!=ESRCH)return -(errno?errno:EIO);
        /* Never call the older fcntl/reconcile helpers with EINTR loops. */
        core->launch_phase=POV6_WAIT_EXIT;return 1;
    }
    if(phase==POV6_OPTIONS) {
        if(ptrace(PTRACE_SETOPTIONS,core->pid,NULL,(void*)(uintptr_t)(PTRACE_O_TRACEEXEC|PTRACE_O_EXITKILL))!=0)
            pov6_failure_locked(core,errno,RT_OWNED_EXEC_FAILURE_PROVIDER_V4);
        else core->launch_phase=POV6_CONTINUE;
        return 1;
    }
    if(phase==POV6_CONTINUE||phase==POV6_KILL_CONTINUE) {
        if(ptrace(PTRACE_CONT,core->pid,NULL,phase==POV6_KILL_CONTINUE?(void*)(uintptr_t)SIGKILL:NULL)!=0) {
            int error=errno;
            if(phase==POV6_KILL_CONTINUE&&error==ESRCH)core->launch_phase=POV6_WAIT_EXIT;
            else if(phase==POV6_KILL_CONTINUE&&error!=EINTR) {
                if(!core->launch_failure)core->launch_failure=error?error:EIO;
                core->launch_phase=POV6_UNCERTAIN;return -core->launch_failure;
            } else pov6_failure_locked(core,error,RT_OWNED_EXEC_FAILURE_PROVIDER_V4);
        } else core->launch_phase=phase==POV6_KILL_CONTINUE?POV6_WAIT_EXIT:POV6_WAIT_EXEC;
        return 1;
    }
    if(phase==POV6_DETACH) {
        if(ptrace(PTRACE_DETACH,core->pid,NULL,NULL)!=0) {
            pov6_failure_locked(core,errno,RT_OWNED_EXEC_FAILURE_PROVIDER_V4);return 1;
        }
        core->exec_confirmed_ns=core->launch_event_ns;
        pov6_close_exec_locked(core);core->launch_phase=0;return 2;
    }
    if(phase==POV6_ERROR_READ) {
        ssize_t count=read(core->launch_exec_fd,core->launch_error_bytes+core->launch_error_count,
            sizeof(int)-(size_t)core->launch_error_count);
        if(count<0) {
            if(errno==EINTR){core->eintr_retries=owned_add_sat(core->eintr_retries,1);return 1;}
            if(errno==EAGAIN||errno==EWOULDBLOCK)return 1;
            if(!core->launch_failure)core->launch_failure=errno?errno:EIO;
            core->launch_phase=POV6_UNCERTAIN;return -core->launch_failure;
        }
        core->launch_error_count+=(int)count;
        if(count==0&&core->launch_error_count!=0&&core->launch_error_count!=(int)sizeof(int)) {
            core->launch_failure=EPROTO;core->launch_phase=POV6_UNCERTAIN;return -EPROTO;
        }
        if(core->launch_error_count==(int)sizeof(int)) {
            int error;memcpy(&error,core->launch_error_bytes,sizeof(error));
            if(!core->launch_failure){core->launch_failure=error>0?error:EPROTO;core->launch_failure_class=error>0?RT_OWNED_EXEC_FAILURE_CHILD_V4:RT_OWNED_EXEC_FAILURE_PROVIDER_V4;}
        } else if(count>0)return 1;
        else if(!core->launch_failure){core->launch_failure=EPROTO;core->launch_failure_class=RT_OWNED_EXEC_FAILURE_PROVIDER_V4;}
        core->runtime_error=core->launch_failure;
        pov6_close_exec_locked(core);core->launch_phase=0;return 2;
    }
    if(phase==POV6_WAIT_STOP||phase==POV6_WAIT_EXEC||phase==POV6_WAIT_EXIT) {
        int status=0;pid_t waited=waitpid(core->pid,&status,WNOHANG|WUNTRACED);
        if(waited==0)return 1;
        if(waited<0) {
            if(errno==EINTR){core->eintr_retries=owned_add_sat(core->eintr_retries,1);return 1;}
            core->launch_failure=errno?errno:EIO;core->launch_phase=POV6_UNCERTAIN;
            /* ECHILD is uncertainty, never permission to signal a recycled PID. */
            return -core->launch_failure;
        }
        if(WIFEXITED(status)||WIFSIGNALED(status)){pov6_reaped_locked(core,status);return 1;}
        if(phase==POV6_WAIT_EXIT&&WIFSTOPPED(status)){core->launch_phase=POV6_KILL_CONTINUE;return 1;}
        if(phase==POV6_WAIT_STOP&&WIFSTOPPED(status)&&WSTOPSIG(status)==SIGSTOP){core->launch_phase=POV6_OPTIONS;return 1;}
        if(phase==POV6_WAIT_EXEC&&WIFSTOPPED(status)&&WSTOPSIG(status)==SIGTRAP&&((unsigned)status>>16)==PTRACE_EVENT_EXEC) {
            int64_t observed=owned_now_ns();
            if(observed<0) {
                core->clock_failed=1;
                pov6_failure_locked(core,EIO,RT_OWNED_EXEC_FAILURE_CLOCK_V4);
            } else {core->launch_event_ns=observed;core->launch_phase=POV6_DETACH;}
            return 1;
        }
        pov6_failure_locked(core,EPROTO,RT_OWNED_EXEC_FAILURE_PROVIDER_V4);return 1;
    }
    return -EPROTO;
}
static void pov6_materialize(Pov4Reservation* reservation,Pov4Slot* owner,RtOwnedSlot* core) {
    int error=core->launch_failure,failure_class=core->launch_failure_class;
    int64_t* w=owner->words;
    w[POV4_EXEC_CONFIRMED_NS]=core->exec_confirmed_ns;
    if(!error) {
        w[POV4_STATUS]=POV4_STATUS_RUNNING;w[POV4_PHASE]=POV4_PHASE_RUNNING;
        w[POV4_EXEC_STATE]=POV4_EXEC_CONFIRMED;w[POV4_VALIDITY]|=POV4_VALID_EXEC;
    } else {
        owner->cleanup_only=1;w[POV4_STATUS]=POV4_STATUS_CLEANUP_PENDING;w[POV4_PHASE]=POV4_PHASE_CLEANUP;
        w[POV4_EXEC_STATE]=failure_class==RT_OWNED_EXEC_FAILURE_CHILD_V4?POV4_EXEC_FAILED:POV4_EXEC_PENDING;
        w[POV4_EXEC_ERRNO]=failure_class==RT_OWNED_EXEC_FAILURE_CHILD_V4?error:0;
        w[POV4_FAILURE_PHASE]=POV4_FAIL_EXECUTION;w[POV4_ERRNO]=error;
        w[POV4_FAILURE_REASON]=failure_class==RT_OWNED_EXEC_FAILURE_CHILD_V4?POV4_REASON_EXEC:
            failure_class==RT_OWNED_EXEC_FAILURE_DEADLINE_V4?POV4_REASON_EXEC_DEADLINE:
            failure_class==RT_OWNED_EXEC_FAILURE_CLOCK_V4?POV4_REASON_CLOCK:POV4_REASON_PROVIDER;
        if(failure_class==RT_OWNED_EXEC_FAILURE_CLOCK_V4) {
            w[POV4_VALIDITY]&=~POV4_VALID_CLOCK;w[POV4_CLOCK_ID]=0;
            w[POV4_CLOCK_NOMINAL_RES_NS]=0;w[POV4_CLOCK_EFFECTIVE_RES_NS]=0;w[POV4_CLOCK_CPU_RES_NS]=0;
        }
    }
    reservation->state=4;
}
#endif
static int64_t pov6_start_deferred_admitted_impl(int64_t token,int64_t executable,int64_t cwd,
        SplArray* binding,int64_t expiry) {
#ifndef __linux__
    (void)token;(void)executable;(void)cwd;(void)binding;(void)expiry;return -ENOTSUP;
#else
    if(!pov6_origin_activate())return -errno;
    Pov4Reservation* r=pov4_reservation_acquire(token);if(!r)return -errno;
    if(r->state!=1){pov4_reservation_release_busy(r);return -EALREADY;}
    int tid=pov6_current_tid();if(tid<=0){pov4_reservation_release_busy(r);return -ENOTSUP;}
    unsigned stamp=pov6_current_thread_stamp();
    if(!stamp){pov4_reservation_release_busy(r);return -errno;}
    r->submit_tid=tid;r->submit_thread_stamp=stamp;r->deferred_launch=1;r->state=2;r->executable_pin=executable;r->cwd_pin=cwd;
    r->submission_expires_unix_ms=expiry;
    int error=expiry<=0?EINVAL:pov5_submission_admission_check(expiry);
    if(error){r->submission_admission_error=error;r->state=3;pov4_reservation_release_busy(r);return -error;}
    Pov4Request request;
    if(!pov4_request_from_value(binding,&request)){r->state=3;pov4_reservation_release_busy(r);return -EPROTO;}
    memcpy(r->request_digest,request.request_digest,32);pov4_request_free(&request);
    SplArray* initial=pov4_start_pinned_impl(executable,cwd,binding,NULL,NULL,0,r);
    if(initial)pov4_tuple4_free(initial);
    int64_t progress=r->state==6?1:r->state==4?2:0;
    if(r->state!=6&&r->state!=4){r->state=3;r->owner_index=UINT32_MAX;}
    pov4_reservation_release_busy(r);return progress;
#endif
}
static int64_t pov6_poll_launch_impl(int64_t token,int retire) {
#ifndef __linux__
    (void)token;(void)retire;return -ENOTSUP;
#else
    if(!pov6_origin_activate())return -errno;
    Pov4Reservation* r=pov4_reservation_acquire(token);if(!r)return -errno;
    if(!r->deferred_launch||r->state==1){pov4_reservation_release_busy(r);return -EINVAL;}
    if(r->state==3){pov4_reservation_release_busy(r);return 0;}
    if(r->state==4||r->state==5){pov4_reservation_release_busy(r);return 2;}
    if(r->state!=6){pov4_reservation_release_busy(r);return -EBUSY;}
    Pov4Slot* owner=pov4_reservation_owner(r);
    RtOwnedSlot* core=owner?owned_token_acquire(owner->core,NULL):NULL;
    if(!core){pov4_reservation_release_busy(r);return -ESTALE;}
    pthread_mutex_lock(core->state_lock);
    int progress=pov6_step_locked(core,retire!=0);
    if(progress==2)pov6_materialize(r,owner,core);
    pthread_mutex_unlock(core->state_lock);owned_token_release(core);
    if(progress==2)pov4_snapshot(owner,NULL);
    pov4_reservation_release_busy(r);return progress;
#endif
}
