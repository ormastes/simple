#define _GNU_SOURCE
#include "../simple_vector_kernel_abi_v1.h"
#include <dlfcn.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>
#define CHECK(x) do { if(!(x)) { fprintf(stderr,"FAIL line=%d %s\n",__LINE__,#x); return 1; } } while(0)
static int64_t oracle(unsigned op,const uint8_t *p,size_t n,uint8_t needle) {
    for(size_t i=0;i<n;i++) {
        if(op==3 && p[i]==needle) return (int64_t)i;
        if(op==4 && n-i>=2 && p[i]==13 && p[i+1]==10) return (int64_t)i;
    }
    return -1;
}
static void request(uint8_t *q,unsigned op,const uint8_t *p,size_t n,uint64_t arg) {
    memset(q,0,64); simple_vector_wr32(q,64); simple_vector_wr32(q+4,op);
    simple_vector_wr64(q+8,n?(uintptr_t)p:0); simple_vector_wr64(q+16,n);
    simple_vector_wr64(q+56,arg);
}
int main(int argc,char **argv) {
    CHECK(argc==3 || argc==4);
    int forced=argc==3?atoi(argv[2]):0;
    int bitmap_supported=0,byte_supported=0;
#if defined(__x86_64__)
    __builtin_cpu_init();
    bitmap_supported=__builtin_cpu_supports("avx512f")!=0;
    byte_supported=bitmap_supported && __builtin_cpu_supports("avx512bw") && !forced;
#endif
    /* Cross-target rows supply independently selected QEMU CPU expectations. */
    if(argc==4) { byte_supported=atoi(argv[2]); bitmap_supported=atoi(argv[3]); }
    void *lib=dlopen(argv[1],RTLD_NOW|RTLD_LOCAL); CHECK(lib);
    simple_vector_query_fn_v1 query=(simple_vector_query_fn_v1)dlsym(lib,"simple_provider_query_v1");
    simple_vector_apply_fn_v1 apply=(simple_vector_apply_fn_v1)dlsym(lib,"simple_vector_apply_v1");
    uint64_t (*iterations)(void)=(uint64_t(*)(void))dlsym(lib,"simple_vector_executed_iterations_v1");
    CHECK(query&&apply&&iterations&&iterations()==0);
    uint8_t pq[44]={0},pr[84],q[64],rbuf[40];
    uint8_t *r=rbuf+8;
    simple_vector_wr32(pq,44); simple_vector_wr64(pq+4,SIMPLE_VECTOR_KERNELS_V1_INTERFACE);
    simple_vector_wr32(pq+12,1); simple_vector_wr64(pq+20,1); simple_vector_wr64(pq+36,15);
    CHECK(query((uintptr_t)pq,(uintptr_t)pr)==0);
    static const uint8_t digest[32]=SIMPLE_VECTOR_ABI_DIGEST_BYTES;
    CHECK(!memcmp(digest,pr+48,32)); int64_t handle=(int64_t)simple_vector_rd64(pr+16);
    long page=sysconf(_SC_PAGESIZE); CHECK(page>=1024);
    uint8_t *mapping=mmap(NULL,(size_t)page*3,PROT_NONE,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
    CHECK(mapping!=MAP_FAILED); uint8_t *area=mapping+page;
    CHECK(!mprotect(area,(size_t)page,PROT_READ|PROT_WRITE));
    const size_t lengths[]={0,1,2,3,31,32,63,64,65,66,127,128,129,255,256,257};
    unsigned cases=0; uint8_t before[512];
    for(unsigned op=3;op<=4;op++) for(size_t l=0;l<sizeof(lengths)/sizeof(lengths[0]);l++) {
        size_t n=lengths[l];
        /* offset zero ends exactly at an inaccessible page; 1/7 test offsets. */
        for(unsigned offset=0;offset<=7;offset+=offset?6:1) {
            uint8_t *p=area+page-n-offset;
            for(unsigned pattern=0;pattern<6;pattern++) {
                memset(area,0xa5,(size_t)page);
                uint8_t needle=pattern==5?0:0xff;
                for(size_t i=0;i<n;i++) p[i]=(uint8_t)(0x80+(i%64));
                if(pattern==1 && n) p[n-1]=op==3?needle:13;
                if(pattern==2 && n>64) { p[63]=op==3?needle:13; if(op==4)p[64]=10; }
                if(pattern==3 && n>128) { p[127]=op==3?needle:13; if(op==4)p[128]=10; }
                if(pattern==4 && n>1) { p[0]=op==3?needle:13; p[1]=op==3?needle:10; }
                if(pattern==5 && n>2) { p[n-2]=op==3?needle:13; p[n-1]=10; }
                memcpy(before,p,n+offset); memset(rbuf,0xd7,sizeof(rbuf));
                request(q,op,p,n,op==3?needle:0);
                int64_t expected=oracle(op,p,n,needle);
                CHECK(apply(handle,(uintptr_t)q,(uintptr_t)r)==0);
                CHECK(simple_vector_rd32(r)==24 && simple_vector_rd32(r+4)==(byte_supported?0u:5u));
                CHECK(simple_vector_rd64(r+8)==0);
                CHECK((int64_t)simple_vector_rd64(r+16)==(byte_supported?expected:-1));
                CHECK(!memcmp(before,p,n+offset));
                for(unsigned i=0;i<8;i++) CHECK(rbuf[i]==0xd7 && rbuf[i+32]==0xd7);
                cases++;
            }
        }
    }
    CHECK(byte_supported?iterations()>0:iterations()==0);
    uint64_t http_iterations=iterations();
    /* Unsupported bytes never disable or call the bitmap F-only route. */
    uint32_t a[16],b[16],out[16];
    for(unsigned i=0;i<16;i++){a[i]=0xffffffffu;b[i]=i;out[i]=0xdeadbeefu;}
    request(q,1,(uint8_t*)a,sizeof(a),0);
    simple_vector_wr64(q+24,(uintptr_t)b); simple_vector_wr64(q+32,sizeof(b));
    simple_vector_wr64(q+40,(uintptr_t)out); simple_vector_wr64(q+48,sizeof(out));
    CHECK(apply(handle,(uintptr_t)q,(uintptr_t)r)==0);
    CHECK(simple_vector_rd32(r+4)==(bitmap_supported?0u:5u));
    for(unsigned i=0;i<16;i++) CHECK(out[i]==(bitmap_supported?i:0xdeadbeefu));
    for(unsigned mode=0;mode<7;mode++) {
        request(q,3,area,64,255); unsigned expected=4;
        if(mode==0) simple_vector_wr64(q+56,256);
        if(mode==1) simple_vector_wr64(q+24,(uintptr_t)area);
        if(mode==2) simple_vector_wr64(q+40,(uintptr_t)area);
        if(mode==3) simple_vector_wr64(q+8,SIMPLE_VECTOR_MAX_ADDRESS-1);
        if(mode==4) simple_vector_wr64(q+16,SIMPLE_VECTOR_MAX_SPAN_BYTES+1);
        if(mode==5) { simple_vector_wr32(q+4,4); simple_vector_wr64(q+56,1); }
        if(mode==6) { simple_vector_wr32(q+4,5); expected=2; }
        CHECK(apply(handle,(uintptr_t)q,(uintptr_t)r)==0 && simple_vector_rd32(r+4)==expected);
    }
    simple_vector_wr64(pq+36,3); CHECK(query((uintptr_t)pq,(uintptr_t)pr)==0);
    request(q,3,area,64,255);
    CHECK(apply((int64_t)simple_vector_rd64(pr+16),(uintptr_t)q,(uintptr_t)r)==0 && simple_vector_rd32(r+4)==3);
    CHECK(!munmap(mapping,(size_t)page*3)); CHECK(!dlclose(lib));
    if(argc==3&&!forced&&!byte_supported) { puts("UNSUPPORTED AVX512F+BW host required; refusal checks completed"); return 77; }
    printf("vector_http_provider=pass mode=%s cases=%u http_vector_iterations=%llu bitmap_supported=%d guard_pages=true input_preserved=true\n",argc==4?"cross-target":forced?"forced-no-bw":"native",cases,(unsigned long long)http_iterations,bitmap_supported);
    return 0;
}
