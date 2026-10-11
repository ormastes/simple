/* Real runtime contract fixture. Link with --wrap=malloc,--wrap=calloc,--wrap=free and the paired runtime.
 * baseline mode records the old NUL loss; candidate mode requires counted bytes.
 * Overflow cases deliberately alter registered metadata, restore it, and require
 * rejection before malloc/copy. They must never be run against the old owner. */
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/resource.h>
#include <unistd.h>
typedef struct SplArray SplArray;
extern SplArray* rt_array_new(int64_t);
extern int8_t rt_array_push(SplArray*, int64_t);
extern void rt_array_free(SplArray*);
extern int64_t rt_string_new(const uint8_t*, uint64_t);
extern int64_t rt_string_len(int64_t);
extern const uint8_t* rt_string_data(int64_t);
extern int64_t rt_string_free(int64_t);
extern int64_t rt_array_join_any(int64_t, int64_t);
extern void* __real_malloc(size_t);
extern void* __real_calloc(size_t,size_t);
extern void __real_free(void*);
static int reject_next, malloc_calls, checks, reject_calloc, rejected_calloc, last_freed;
static void* last_allocation;
void* __wrap_calloc(size_t n,size_t size) {
    if(reject_calloc) { rejected_calloc++; return NULL; }
    return __real_calloc(n,size);
}
void __wrap_free(void* p) { if(p && p==last_allocation) last_freed++; __real_free(p); }
static size_t malloc_bytes;
void* __wrap_malloc(size_t n) {
    malloc_calls++; malloc_bytes += n;
    if (reject_next) { reject_next = 0; return NULL; }
    last_allocation=__real_malloc(n); last_freed=0; return last_allocation;
}
static int64_t text(const void* p, size_t n) { return rt_string_new(p,n); }
static int64_t raw(const char* p) { return (int64_t)(uintptr_t)p; }
static void expect(int64_t out, const void* bytes, size_t len) {
    assert(rt_string_len(out) == (int64_t)len);
    assert(!len || memcmp(rt_string_data(out), bytes, len) == 0);
    assert(rt_string_data(out)[len] == 0);
    rt_string_free(out); checks++;
}
static SplArray* array(const int64_t* values, size_t n) {
    SplArray* a = rt_array_new((int64_t)n); assert(a);
    for (size_t i=0;i<n;i++) assert(rt_array_push(a,values[i]));
    return a;
}
static void join(const int64_t* values,size_t n,int64_t sep,const void* bytes,size_t len) {
    SplArray* a=array(values,n);
    expect(rt_array_join_any((int64_t)(uintptr_t)a,sep),bytes,len);
    rt_array_free(a);
}
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return t.tv_sec+t.tv_nsec/1e9; }
static long peak_rss(void) {
    FILE* f=fopen("/proc/self/status","r"); assert(f); char line[256]; long peak=0;
    while(fgets(line,sizeof(line),f)) if(sscanf(line,"VmHWM: %ld kB",&peak)==1) break;
    fclose(f); assert(peak>0); return peak;
}
static long rss(void) { FILE* f=fopen("/proc/self/statm","r"); long pages=0, unused; assert(f); assert(fscanf(f,"%ld %ld",&unused,&pages)==2); fclose(f); return pages*(sysconf(_SC_PAGESIZE)/1024); }
int main(int argc,char** argv) {
    if(argc>1 && !strcmp(argv[1],"registration-oom")) {
        int64_t value=raw("payload"), held[4096]; size_t count=0;
        SplArray* a=array(&value,1); reject_calloc=1;
        while(count<4096) {
            int64_t out=rt_array_join_any((int64_t)(uintptr_t)a,raw(","));
            if(rejected_calloc) {
                assert(rt_string_len(out)==-1 && last_freed==1); break;
            }
            assert(rt_string_len(out)==7); held[count++]=out;
        }
        reject_calloc=0; assert(rejected_calloc==1 && count<4096);
        for(size_t i=0;i<count;i++) rt_string_free(held[i]);
        rt_array_free(a); printf("registration failure cleanup PASS after %zu retained joins\n",count); return 0;
    }
    int baseline=argc>1 && !strcmp(argv[1],"baseline");
    if(argc>1 && !strcmp(argv[1],"bench")) {
        char payload[1025]; memset(payload,'x',1024); payload[1024]=0;
        int64_t tagged=text(payload,1024), vals[512];
        int raw_only=argc>2 && !strcmp(argv[2],"raw");
        for(int i=0;i<512;i++) vals[i]=raw_only?raw(payload):tagged;
        SplArray* a=array(vals,512);
        for(int i=0;i<8;i++) {
            int64_t out=rt_array_join_any((int64_t)(uintptr_t)a,raw(","));
            assert(rt_string_len(out)==524799); rt_string_free(out);
        }
        long steady_before=rss(); malloc_calls=0; malloc_bytes=0;
        double start=now();
        for(int i=0;i<8192;i++) {
            int64_t out=rt_array_join_any((int64_t)(uintptr_t)a,raw(","));
            const uint8_t* p=rt_string_data(out);
            assert(rt_string_len(out)==524799 && p[0]=='x' && p[1024]==',' && p[524798]=='x' && p[524799]==0);
            rt_string_free(out);
        }
        double elapsed=now()-start; long steady_after=rss();
        long peak=peak_rss();
        printf("{\"seconds\":%.9f,\"peak_kib\":%ld,\"steady_before_kib\":%ld,\"steady_after_kib\":%ld,\"malloc_calls\":%d,\"malloc_bytes\":%zu}\n",elapsed,peak,steady_before,steady_after,malloc_calls,malloc_bytes);
        rt_array_free(a); rt_string_free(tagged);
        return 0;
    }
    int64_t abc=text("abc",3), nul=text("a\0b",3), empty=text("",0), utf=text("\xc3\xa9\xe9\x9b\xaa",5), nsep=text("|\0!",3);
    join(NULL,0,raw(","),"",0);
    join(&empty,1,raw(","),"",0);
    join(&abc,1,raw(","),"abc",3);
    int64_t mixed[]={raw("raw"),abc,utf};
    join(mixed,3,raw("/"),"raw/abc/\xc3\xa9\xe9\x9b\xaa",13);
    int64_t blanks[]={empty,0,raw("tail")};
    join(blanks,3,raw(","),",,tail",6);
    int64_t ns[]={nul,raw("cd")};
    join(ns,2,raw(","),baseline?"a,cd":"a\0b,cd",baseline?4:6);
    join(mixed,2,nsep,baseline?"raw|abc":"raw|\0!abc",baseline?7:9);
    join(ns,2,nsep,baseline?"a|cd":"a\0b|\0!cd",baseline?4:8);
    expect(rt_array_join_any(0,raw(",")),"",0);
    join(mixed,2,0,"rawabc",6);
    /* Every possible literal alignment remains valid, including tag-like bits. */
    char align[24]; memset(align,'q',23); align[23]=0;
    for(int i=0;i<8;i++) { int64_t v=raw(align+i); join(&v,1,empty,align+i,23-i); }
    SplArray* a=array(&abc,1); reject_next=1;
    expect(rt_array_join_any((int64_t)(uintptr_t)a,empty),"",0);
    assert(!reject_next); rt_array_free(a);
    assert(rt_string_len(nul)==3 && memcmp(rt_string_data(nul),"a\0b",3)==0);
    if(!baseline) {
        struct header { uint32_t kind,reserved; uint64_t len; };
        struct header* h=(void*)((uintptr_t)abc & ~(uintptr_t)7);
        uint64_t saved=h->len;
        int64_t duplicate[]={abc,abc}; a=array(duplicate,2);
        size_t lengths[]={SIZE_MAX,SIZE_MAX-sizeof(*h)-1,(SIZE_MAX-sizeof(*h)-1)/2+1};
        for(size_t i=0;i<3;i++) {
            h->len=lengths[i]; malloc_calls=0;
            int64_t out=rt_array_join_any((int64_t)(uintptr_t)a,empty);
            assert(malloc_calls==0); h->len=saved; expect(out,"",0);
        }
        h->len=SIZE_MAX; malloc_calls=0;
        int64_t out=rt_array_join_any((int64_t)(uintptr_t)a,abc);
        assert(malloc_calls==0); h->len=saved; expect(out,"",0);
        rt_array_free(a);
    }
    rt_string_free(abc); rt_string_free(nul); rt_string_free(utf); rt_string_free(nsep);
    printf("%s checks=%d PASS\n",baseline?"baseline":"candidate",checks);
    return 0;
}
