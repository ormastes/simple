#include "../simple_vector_kernel_abi_v1.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <dlfcn.h>
static unsigned loads,checks;
void simple_vector_test_loaded(void) { loads++; }
#define CHECK(x) do { checks++; if(!(x)) { fprintf(stderr,"FAIL line=%d check=%u\n",__LINE__,checks); return 1; } } while(0)
static void request(uint8_t q[64],uint32_t op,uint32_t *a,uint32_t *b,uint32_t *out,size_t n) {
    memset(q,0,64); simple_vector_wr32(q,64); simple_vector_wr32(q+4,op);
    simple_vector_wr64(q+8,n?(uintptr_t)a:0); simple_vector_wr64(q+16,n*4);
    simple_vector_wr64(q+24,n?(uintptr_t)b:0); simple_vector_wr64(q+32,n*4);
    simple_vector_wr64(q+40,n?(uintptr_t)out:0); simple_vector_wr64(q+48,n*4);
}
int main(int argc,char **argv) {
    CHECK(argc==3); int supported=atoi(argv[2]);
    CHECK(loads==0);
    void *lib=dlopen(argv[1],RTLD_NOW|RTLD_LOCAL);
    if(!lib) fprintf(stderr,"dlopen: %s\n",dlerror());
    CHECK(lib!=NULL); CHECK(loads==1);
    simple_vector_query_fn_v1 query=(simple_vector_query_fn_v1)dlsym(lib,"simple_provider_query_v1");
    simple_vector_apply_fn_v1 apply=(simple_vector_apply_fn_v1)dlsym(lib,"simple_vector_apply_v1");
    uint64_t (*iterations)(void)=(uint64_t (*)(void))dlsym(lib,"simple_vector_executed_iterations_v1");
    CHECK(query&&apply&&iterations); CHECK(iterations()==0);
    uint8_t pq[44]={0},pr[84],q[64],r[24];
    simple_vector_wr32(pq,44); simple_vector_wr64(pq+4,SIMPLE_VECTOR_KERNELS_V1_INTERFACE);
    simple_vector_wr32(pq+12,1); simple_vector_wr64(pq+20,1); simple_vector_wr64(pq+36,3);
    CHECK(query((uintptr_t)pq,(uintptr_t)pr)==0);
    static const uint8_t digest[32]=SIMPLE_VECTOR_ABI_DIGEST_BYTES;
    CHECK(!memcmp(pr+48,digest,32)); CHECK(simple_vector_rd32(pr+12)==84);
    CHECK(simple_vector_rd64(pr+32)!=0&&simple_vector_rd64(pr+40)!=0);
    int64_t handle=(int64_t)simple_vector_rd64(pr+16);
    uint32_t a[1030],b[1030],out[1030];
    const size_t lengths[]={0,1,3,4,5,15,16,17,31,32,33,127,128,129,1023,1024,1025};
    for(size_t k=0;k<sizeof(lengths)/sizeof(lengths[0]);k++) {
        size_t n=lengths[k];
        for(unsigned offset=1;offset<=2;offset++) for(unsigned op=1;op<=2;op++) {
            for(size_t i=0;i<1030;i++) {
                a[i]=i%4==0?0:i%4==1?UINT32_MAX:i%4==2?UINT32_C(0x80000000):(uint32_t)(i*104729);
                b[i]=(uint32_t)(i*17011)^UINT32_C(0xa5a55a5a); out[i]=UINT32_C(0xdeadbeef);
            }
            request(q,op,a+offset,b+offset,out+offset,n);
            CHECK(apply(handle,(uintptr_t)q,(uintptr_t)r)==0);
            CHECK(simple_vector_rd32(r)==24);
            CHECK(simple_vector_rd32(r+4)==(supported?0:5));
            CHECK(simple_vector_rd64(r+8)==(supported?n*4:0));
            for(size_t i=0;i<1030;i++) {
                uint32_t expected=UINT32_C(0xdeadbeef);
                if(supported&&i>=offset&&i<offset+n) expected=op==1?(a[i]&b[i]):(a[i]|b[i]);
                CHECK(out[i]==expected);
            }
        }
    }
    /* Invalid spans/capabilities fail before feature dispatch, on every CPU. */
    for(unsigned mode=0;mode<7;mode++) {
        request(q,1,a,b,out,4);
        uint32_t expected=4;
        if(mode==0) simple_vector_wr64(q+40,(uintptr_t)a); /* exact overlap */
        if(mode==1) simple_vector_wr64(q+40,(uintptr_t)(a+1)); /* partial overlap */
        if(mode==2) simple_vector_wr64(q+48,12);
        if(mode==3) simple_vector_wr64(q+8,(uintptr_t)a+1);
        if(mode==4) simple_vector_wr64(q+24,UINT64_MAX-3);
        if(mode==5) { simple_vector_wr32(q+4,99); expected=2; }
        if(mode==6) { simple_vector_wr32(q,63); expected=1; }
        memset(out,0xa5,sizeof(out));
        CHECK(apply(handle,(uintptr_t)q,(uintptr_t)r)==0);
        CHECK(simple_vector_rd32(r+4)==expected); CHECK(simple_vector_rd64(r+8)==0);
        CHECK(out[0]==UINT32_C(0xa5a5a5a5));
    }
    simple_vector_wr64(pq+36,1); CHECK(query((uintptr_t)pq,(uintptr_t)pr)==0);
    request(q,2,a,b,out,4);
    CHECK(apply((int64_t)simple_vector_rd64(pr+16),(uintptr_t)q,(uintptr_t)r)==0);
    CHECK(simple_vector_rd32(r+4)==3);
    simple_vector_wr64(pq+36,4); CHECK(query((uintptr_t)pq,(uintptr_t)pr)==5);
    uint64_t ran=iterations(); CHECK(supported?ran>0:ran==0); CHECK(loads==1);
    CHECK(dlclose(lib)==0);
    printf("PASS bitmap-provider checks=%u vector_iterations=%llu supported=%d loads=%u\n",checks,(unsigned long long)ran,supported,loads);
    return 0;
}
