#define _POSIX_C_SOURCE 200809L
/* Link production runtime_simd_utf8.c + runtime_simd_case.c. No copied kernels.
 * Build default and SPL_SIMD_TEXT_CASE_PROVIDER variants; each process starts
 * cold. Each worker owns its string, avoiding the unrelated reserved-cache
 * sharing contract while racing only dispatch initialization. */
#ifdef SIMPLE_SIMD_NO_DEMAND
#include <stdio.h>
int main(void) { puts("hello"); return 0; }
#else
#include "runtime_simd_dispatch.h"
#include <pthread.h>
#include <stdatomic.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
extern int64_t rt_text_validate_utf8_bytes(const uint8_t *, uint64_t);
extern int64_t rt_text_validate_utf8(int64_t);
extern int64_t rt_text_find_invalid_utf8(int64_t);
extern int64_t rt_text_count_codepoints(int64_t);
#ifdef SPL_SIMD_TEXT_CASE_PROVIDER
extern int64_t rt_text_is_ascii(int64_t);
extern int64_t rt_text_to_upper_ascii(int64_t);
extern int64_t rt_text_to_lower_ascii(int64_t);
#endif
static atomic_int ready, start, failures;
#define CHECK(x) do { if (!(x)) { fprintf(stderr,"FAIL line=%d\n",__LINE__); atomic_fetch_add(&failures,1); return NULL; } } while(0)
static void *worker(void *arg) {
    unsigned first_case = (unsigned)(uintptr_t)arg & 1u;
    (void)first_case;
    RtCoreStringSimd *s=malloc(sizeof(*s)+260);
    if(!s) { atomic_fetch_add(&failures,1); atomic_fetch_add(&ready,1); return NULL; }
    s->kind=RT_VALUE_HEAP_STRING_SIMD;
    int64_t value=(int64_t)((uintptr_t)s|RT_VALUE_TAG_HEAP_SIMD);
    atomic_fetch_add(&ready,1);
    s->len=1; s->reserved=0; s->data[0]='a'; s->data[1]=0;
    while(!atomic_load_explicit(&start,memory_order_acquire)) {}
#ifdef SPL_SIMD_TEXT_CASE_PROVIDER
    if(first_case) CHECK(rt_text_is_ascii(value)==1);
#endif
    CHECK(rt_text_validate_utf8(value)==1);
    CHECK(rt_text_validate_utf8(0)==1);
    CHECK(rt_text_find_invalid_utf8(0)==-1);
    CHECK(rt_text_count_codepoints(0)==0);
#ifdef SPL_SIMD_TEXT_CASE_PROVIDER
    CHECK(rt_text_is_ascii(0)==1);
    CHECK(rt_text_to_upper_ascii(0)==0 && rt_text_to_lower_ascii(0)==0);
#endif
    /* Complete/crossing blocks and truncations, including starts29/30/31. */
    for(unsigned pos=0;pos<=65;pos++) {
        memset(s->data,'a',130);
        memcpy(s->data+pos,"\xf0\x9f\x98\x80",4);
        for(unsigned suffix=0;suffix<=33;suffix++) {
            s->len=pos+4+suffix; s->reserved=0;
            CHECK(rt_text_validate_utf8(value)==1);
            CHECK(rt_text_find_invalid_utf8(value)==-1);
            CHECK(rt_text_count_codepoints(value)==(int64_t)s->len-3);
        }
        for(unsigned used=1;used<4;used++) {
            s->len=pos+used; s->reserved=0;
            CHECK(rt_text_validate_utf8(value)==0);
            CHECK(rt_text_find_invalid_utf8(value)==(int64_t)pos);
        }
    }
    for(unsigned n=0;n<=129;n++) {
        memset(s->data,'a',n); s->data[n]=0; s->len=n; s->reserved=0;
        CHECK(rt_text_validate_utf8_bytes((const uint8_t*)s->data,n)==1);
        CHECK(rt_text_count_codepoints(value)==(int64_t)n);
        CHECK(rt_text_find_invalid_utf8(value)==-1);
#ifdef SPL_SIMD_TEXT_CASE_PROVIDER
        CHECK(rt_text_is_ascii(value)==1);
        int64_t upper=rt_text_to_upper_ascii(value);
        RtCoreStringSimd *u=simd_as_string(upper);
        CHECK(u && u->len==n);
        for(unsigned i=0;i<n;i++) CHECK(u->data[i]=='A');
        int64_t lower=rt_text_to_lower_ascii(upper);
        RtCoreStringSimd *l=simd_as_string(lower);
        CHECK(l && l->len==n && !memcmp(l->data,s->data,n));
        if(l!=u && l!=s) free(l);
        if(u!=s) free(u);
#endif
        if(n>=4) {
            memcpy(s->data+n-4,"\xf0\x9f\x98\x80",4); s->reserved=0;
            CHECK(rt_text_validate_utf8(value)==1);
            CHECK(rt_text_count_codepoints(value)==(int64_t)n-3);
        }
        for(unsigned pos=0;pos<n;pos++) {
            memset(s->data,'a',n); s->data[pos]=(char)0xff; s->reserved=0;
            CHECK(rt_text_validate_utf8(value)==0);
            CHECK(rt_text_find_invalid_utf8(value)==(int64_t)pos);
        }
    }
    free(s); return NULL;
}
int main(void) {
    if(g_simd_text.utf8_validate || g_simd_text.is_ascii) {
        fputs("FAIL eager text initialization\n",stderr); return 1;
    }
    pthread_t threads[16];
    for(unsigned i=0;i<16;i++) if(pthread_create(&threads[i],NULL,worker,(void*)(uintptr_t)i)) return 2;
    while(atomic_load(&ready)!=16) {}
    atomic_store_explicit(&start,1,memory_order_release);
    for(unsigned i=0;i<16;i++) if(pthread_join(threads[i],NULL)) return 3;
    if(atomic_load(&failures)) return 4;
    puts("simd_lazy_init=pass threads=16 lengths=0..129 malformed=all_positions");
    return 0;
}
#endif
