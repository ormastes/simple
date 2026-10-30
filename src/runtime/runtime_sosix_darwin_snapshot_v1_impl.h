/* Cooperative Darwin snapshot ABI. This is deliberately separate from V4.
 * Same-UID trusted callers, trusted temporary ancestors, exclusive wait ownership,
 * and descendants remaining in their initial group are preconditions.
 * Arrays must contain their declared Simple types ([text] or [i64]); text
 * access follows the existing runtime string ABI including literal pointers. No seals
 * or escaped-descendant containment are claimed. Registry serializes all waits.
 */
#ifndef RUNTIME_SOSIX_DARWIN_SNAPSHOT_V1_IMPL_H
#define RUNTIME_SOSIX_DARWIN_SNAPSHOT_V1_IMPL_H
#include <errno.h>
#include <stdint.h>
static SplArray* ds1_words(const int64_t* words, int64_t count) {
    SplArray* a = rt_array_new(count); if (!a) return NULL;
    for (int64_t i = 0; i < count; i++) if (!rt_array_push(a, rt_value_int(words[i]))) {
        rt_array_free(a); return NULL;
    }
    return a;
}
#ifdef __APPLE__
#include "runtime_sosix_darwin_process_private.h"
#include <pthread.h>
#include <stdatomic.h>
#define DS1_SLOTS 32
static pthread_mutex_t ds1_lock = PTHREAD_MUTEX_INITIALIZER;
/* Reject fork-inherited registries before touching a possibly inherited lock.
 * Never unlink snapshots or signal process groups owned by the parent. */
static _Atomic int64_t ds1_origin_pid;
static int ds1_process_allowed(void) {
    int64_t self=(int64_t)getpid(), origin=atomic_load_explicit(&ds1_origin_pid,memory_order_acquire);
    if (!origin) {
        int64_t expected=0;
        if (atomic_compare_exchange_strong_explicit(&ds1_origin_pid,&expected,self,memory_order_acq_rel,memory_order_acquire)) return 1;
        origin=expected;
    }
    return origin==self;
}
typedef struct {
    int64_t handle;
    SosixDarwinImage image;
    SosixDarwinProcess process;
} Ds1Slot;
static Ds1Slot ds1_slots[DS1_SLOTS];
static Ds1Slot* ds1_find(int64_t handle) {
    if (handle <= 0) return NULL;
    for (int i = 0; i < DS1_SLOTS; i++) if (ds1_slots[i].handle == handle) return &ds1_slots[i];
    return NULL;
}
static char* ds1_text(int64_t value, size_t *total) {
    int64_t n = rt_string_len(value); const uint8_t* data = rt_string_data(value);
    if (n < 0 || !data || n > 1024 * 1024 || *total > 1024 * 1024 - (size_t)n || memchr(data, 0, (size_t)n)) return NULL;
    char* text = malloc((size_t)n + 1); if (!text) return NULL;
    memcpy(text, data, (size_t)n); text[n] = 0; *total += (size_t)n; return text;
}
static void ds1_free_texts(char** texts, int64_t n) {
    if (texts) { for (int64_t i = 0; i < n; i++) free(texts[i]); free(texts); }
}
static char** ds1_texts(SplArray* a, int64_t begin, int64_t count, size_t* total) {
    char** out = calloc((size_t)count + 1, sizeof(char*)); if (!out) return NULL;
    for (int64_t i = 0; i < count; i++) if (!(out[i] = ds1_text(rt_array_get(a, begin + i), total))) {
        ds1_free_texts(out, count); return NULL;
    }
    return out;
}
static SplArray* ds1_receipt(Ds1Slot* s, int error) {
    if (!s) { const int64_t words[18] = {1,error,0}; return ds1_words(words,18); }
    SosixDarwinProcess* p = &s->process;
    int64_t code = p->reaped ? (WIFEXITED(p->wait_status) ? WEXITSTATUS(p->wait_status) : 128 + WTERMSIG(p->wait_status)) : -1;
    const int64_t words[] = {1,error,s->handle,p->frozen,p->reaped,p->group_retired,code,
        p->timed_out,p->cancel_requested,p->term_sent,p->kill_sent,(int64_t)p->stdout_seen,
        (int64_t)p->stderr_seen,(int64_t)p->stdout_kept,(int64_t)p->stderr_kept,
        p->stdout_error,p->stderr_error,p->cleanup_error};
    return ds1_words(words,18);
}
#endif
SplArray* rt_sosix_darwin_snapshot_v1_capabilities_value(void) {
#ifdef __APPLE__
    int allowed=ds1_process_allowed();
    const int64_t words[] = {1,allowed,allowed,0,0,1,allowed ? 0 : ENOTSUP,1,1,0};
#else
    const int64_t words[] = {1,0,0,0,0,1,ENOTSUP,0,0,0};
#endif
    return ds1_words(words,10);
}
/* invocation = [absolute executable, cwd, argument...]; argv[0] is executable.
 * profile must explicitly equal 1 (trusted cooperative snapshot).
 * environment is complete, never implicitly inherited. limits are nanoseconds,
 * then independent stdout/stderr byte caps. start returns [1,errno,handle]. */
static SplArray* ds1_start(int64_t profile, const unsigned char* expected_digest, SplArray* invocation, SplArray* environment, SplArray* limits) {
    const int64_t initial[] = {1,ENOTSUP,0}; SplArray* result = ds1_words(initial,3);
    if (!result) return NULL; /* Reserve receipt before acquiring any child. */
#ifdef __APPLE__
    int error = EINVAL; Ds1Slot* slot = NULL;
    if ((profile != 1 && profile != 2) || (profile==2 && !expected_digest) || !ds1_process_allowed()) { error=ENOTSUP; goto done; }
    if(profile==2) {
        posix_spawnattr_t probe;unsigned char hash[20]={0},bytes[82];error=posix_spawnattr_init(&probe);
        if(!error){error=sosix_darwin_amfi_attach(&probe,hash,bytes);posix_spawnattr_destroy(&probe);}
        if(error)goto done;
        error=EINVAL;
    }
    int64_t n = invocation ? rt_array_len(invocation) : -1;
    int64_t e = environment ? rt_array_len(environment) : -1;
    if (n < 2 || n > 1026 || e < 0 || e > 1024 || !limits || rt_array_len(limits) != 5) goto done;
    int64_t l[5]; for (int i=0;i<5;i++) {
        int64_t value=rt_array_get(limits,i);
        if (!rt_value_is_int(value)) goto done;
        l[i] = rt_value_as_int(value);
    }
    if (l[0] <= 0 || l[1] < 0 || l[2] <= 0 || l[3] < 0 || l[4] < 0 || l[3] > 16*1024*1024 || l[4] > 16*1024*1024) goto done;
    size_t total = 0;
    char** in = ds1_texts(invocation,0,n,&total);
    char** env = ds1_texts(environment,0,e,&total);
    if (!in || !env) { ds1_free_texts(in,n); ds1_free_texts(env,e); goto done; }
    if (in[0][0] != '/' || !in[1][0]) goto free_inputs;
    for (int64_t i=0;i<e;i++) {
        char* equals=strchr(env[i],'='); if (!equals || equals==env[i]) goto free_inputs;
        size_t key=(size_t)(equals-env[i]);
        for (int64_t j=0;j<i;j++) if (!strncmp(env[j],env[i],key) && env[j][key]=='=') goto free_inputs;
    }
    struct sigaction disposition;
    if (sigaction(SIGCHLD,NULL,&disposition)) { error=errno; goto free_inputs; }
    if (disposition.sa_handler != SIG_DFL || (disposition.sa_flags & SA_NOCLDWAIT)) { error=ENOTSUP; goto free_inputs; }
    error = pthread_mutex_lock(&ds1_lock); if (error) goto free_inputs;
    for (int i=0;i<DS1_SLOTS;i++) if (!ds1_slots[i].handle) { slot=&ds1_slots[i]; break; }
    if (!slot) { error=EMFILE; goto unlock; }
    int64_t handle=0;
    for (int attempt=0;attempt<16;attempt++) {
        arc4random_buf(&handle,sizeof(handle)); handle &= ((INT64_C(1)<<47)-1);
        if (handle && !ds1_find(handle)) break;
        handle=0;
    }
    if (!handle) { error=EAGAIN; goto unlock; }
    int source = open(in[0],O_RDONLY|O_CLOEXEC|O_NOFOLLOW|O_NONBLOCK);
    if (source < 0) { error=errno; goto unlock; }
    struct stat source_stat;
    if (fstat(source,&source_stat)) error=errno;
    else if (!S_ISREG(source_stat.st_mode) || source_stat.st_size<=0) error=EINVAL;
    else error=profile==2?sosix_darwin_image_create_bound(source,expected_digest,&slot->image):sosix_darwin_image_create(source,&slot->image);
    close(source);
    if (error) goto unlock;
    int cwd=open(in[1],O_RDONLY|O_DIRECTORY|O_CLOEXEC);
    if (cwd < 0) error=errno;
    else {
        /* Compact invocation into argv without losing the separate cwd string. */
        char* cwd_text=in[1]; in[1]=in[0];
        SosixDarwinProcessLimits bounds={l[0],l[1],l[2],(size_t)l[3],(size_t)l[4]};
        error=sosix_darwin_process_start(&slot->process,&slot->image,slot->image.generation,cwd,in+1,env,bounds);
        in[1]=cwd_text; close(cwd);
    }
    if (error) { (void)sosix_darwin_image_close(&slot->image,slot->image.generation); goto unlock; }
    slot->handle=handle;
    /* Existing three-element result has capacity; these sets cannot allocate. */
    rt_array_set(result,2,rt_value_int(handle));
unlock:
    pthread_mutex_unlock(&ds1_lock);
free_inputs:
    ds1_free_texts(in,n); ds1_free_texts(env,e);
done:
    rt_array_set(result,1,rt_value_int(error));
#else
    (void)profile; (void)expected_digest; (void)invocation; (void)environment; (void)limits;
#endif
    return result;
}

SplArray* rt_sosix_darwin_snapshot_v1_start_value(int64_t profile, SplArray* invocation, SplArray* environment, SplArray* limits) {
    /* Preserve the old profile contract: no implicit upgrade or fallback. */
    if(profile!=1){const int64_t words[]={1,ENOTSUP,0};return ds1_words(words,3);}
    return ds1_start(1,NULL,invocation,environment,limits);
}

/* Explicit content-authenticated AMFI image admission. It shares only the
 * cooperative group lifecycle registry; this is not strict Tree admission.
 * expected_sha256 is a canonical lowercase hex digest supplied by the caller's
 * trusted artifact manifest, never recomputed from the mutable source path. */
SplArray* rt_sosix_darwin_bound_image_v1_start_value(int64_t expected_sha256, SplArray* invocation, SplArray* environment, SplArray* limits) {
#ifdef __APPLE__
    unsigned char digest[32];int error=EINVAL;
    if(rt_string_len(expected_sha256)!=64)goto invalid;
    const uint8_t *text=rt_string_data(expected_sha256);if(!text)goto invalid;
    for(size_t i=0;i<32;i++) {
        unsigned value=0;
        for(size_t j=0;j<2;j++) {
            unsigned c=text[i*2+j];
            if(c>='0'&&c<='9')value=value*16+c-'0';
            else if(c>='a'&&c<='f')value=value*16+c-'a'+10;
            else goto invalid;
        }
        digest[i]=(unsigned char)value;
    }
    return ds1_start(2,digest,invocation,environment,limits);
invalid:
    {const int64_t words[]={1,error,0};return ds1_words(words,3);}
#else
    (void)expected_sha256;(void)invocation;(void)environment;(void)limits;
    const int64_t words[]={1,ENOTSUP,0};return ds1_words(words,3);
#endif
}

SplArray* rt_sosix_darwin_snapshot_v1_poll_value(int64_t handle, int64_t wait_ns) {
#ifdef __APPLE__
    if (!ds1_process_allowed()) return ds1_receipt(NULL,ESTALE);
    int error=pthread_mutex_lock(&ds1_lock); if (error) return ds1_receipt(NULL,error);
    Ds1Slot* s=ds1_find(handle);
    error=s ? sosix_darwin_process_poll(&s->process,s->process.generation,wait_ns) : ESTALE;
    SplArray* result=ds1_receipt(s,error); pthread_mutex_unlock(&ds1_lock); return result;
#else
    (void)handle; (void)wait_ns; const int64_t words[18]={1,ENOTSUP,0}; return ds1_words(words,18);
#endif
}
SplArray* rt_sosix_darwin_snapshot_v1_cancel_value(int64_t handle) {
#ifdef __APPLE__
    if (!ds1_process_allowed()) return ds1_receipt(NULL,ESTALE);
    int error=pthread_mutex_lock(&ds1_lock); if (error) return ds1_receipt(NULL,error);
    Ds1Slot* s=ds1_find(handle);
    error=s ? sosix_darwin_process_cancel(&s->process,s->process.generation) : ESTALE;
    SplArray* result=ds1_receipt(s,error); pthread_mutex_unlock(&ds1_lock); return result;
#else
    return rt_sosix_darwin_snapshot_v1_poll_value(handle,0);
#endif
}
/* Output envelope [version,errno,byte...]; empty success differs from failure. */
SplArray* rt_sosix_darwin_snapshot_v1_output_value(int64_t handle, int64_t stream) {
#ifdef __APPLE__
    if (!ds1_process_allowed()) { const int64_t words[]={1,ESTALE}; return ds1_words(words,2); }
    int error=pthread_mutex_lock(&ds1_lock);
    if (error) { const int64_t words[]={1,error}; return ds1_words(words,2); }
    Ds1Slot* s=ds1_find(handle); SplArray* result=NULL;
    error=!s ? ESTALE : ((stream!=1 && stream!=2) ? EINVAL : (!s->process.frozen ? EBUSY : 0));
    if (error) { const int64_t words[]={1,error}; result=ds1_words(words,2); }
    else {
        size_t n=stream==1 ? s->process.stdout_kept : s->process.stderr_kept;
        unsigned char* data=stream==1 ? s->process.stdout_bytes : s->process.stderr_bytes;
        result=rt_array_new((int64_t)n+2);
        if (result && (!rt_array_push(result,rt_value_int(1)) || !rt_array_push(result,rt_value_int(0)))) {
            rt_array_free(result); result=NULL;
        }
        if (result) for (size_t i=0;i<n;i++) if (!rt_array_push(result,rt_value_int(data[i]))) {
            rt_array_free(result); result=NULL; break;
        }
    }
    pthread_mutex_unlock(&ds1_lock); return result;
#else
    (void)handle; (void)stream; const int64_t words[]={1,ENOTSUP}; return ds1_words(words,2);
#endif
}
int64_t rt_sosix_darwin_snapshot_v1_ack_value(int64_t handle) {
#ifdef __APPLE__
    if (!ds1_process_allowed()) return ESTALE;
    int error=pthread_mutex_lock(&ds1_lock); if (error) return error;
    Ds1Slot* s=ds1_find(handle);
    if (!s) error=ESTALE;
    else {
        error=sosix_darwin_process_ack(&s->process,s->process.generation);
        if (!error) {
            error=sosix_darwin_image_close(&s->image,s->image.generation);
            memset(s,0,sizeof(*s));
        }
    }
    pthread_mutex_unlock(&ds1_lock); return error;
#else
    (void)handle; return ENOTSUP;
#endif
}
#endif
