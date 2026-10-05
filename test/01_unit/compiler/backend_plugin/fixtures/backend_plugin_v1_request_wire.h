#ifndef SBP_FIXTURE_REQUEST_WIRE_H
#define SBP_FIXTURE_REQUEST_WIRE_H
static void fixture_u32(uint8_t *p, uint32_t n) {
    for (unsigned i=0;i<4;++i) p[i]=(uint8_t)(n>>(8*i));
}
static size_t fixture_request(uint8_t *out) {
    static const uint8_t features[]={2,0,0,0,5,0,0,0,'+','s','s','e','2',4,0,0,0,'-','a','v','x'};
    const char *text[6]={"cranelift","x86_64-pc-windows-msvc","znver3",NULL,"speed","mir-config-v1"};
    memset(out,0,512);
    fixture_u32(out,SIMPLE_BACKEND_REQUEST_MAGIC_V1);
    fixture_u32(out+4,1);fixture_u32(out+8,1);fixture_u32(out+12,2);
    fixture_u32(out+16,10);
    size_t cursor=SIMPLE_BACKEND_REQUEST_HEADER_SIZE_V1;
    for(unsigned i=0;i<6;++i){
        size_t n=i==3?sizeof(features):strlen(text[i]);
        fixture_u32(out+24+4*i,(uint32_t)n);
        memcpy(out+cursor,i==3?(const void*)features:(const void*)text[i],n);cursor+=n;
    }
    return cursor;
}
static size_t fixture_request_mutate(uint8_t *out,size_t n,const char *mode) {
    if(!mode)return n;
    if(!strcmp(mode,"legacy-request"))return 16;
    if(!strcmp(mode,"bad-version"))fixture_u32(out+4,2);
    if(!strcmp(mode,"bad-abi"))fixture_u32(out+8,2);
    if(!strcmp(mode,"bad-role"))fixture_u32(out+12,3);
    if(!strcmp(mode,"bad-caps"))fixture_u32(out+20,1);
    if(!strcmp(mode,"bad-length"))fixture_u32(out+24,UINT32_MAX);
    if(!strcmp(mode,"bad-empty"))fixture_u32(out+24,0);
    if(!strcmp(mode,"bad-utf8"))out[48]=0xff;
    if(!strcmp(mode,"bad-nul"))out[48]=0;
    if(!strcmp(mode,"trailing-request"))out[n++]=0;
    if(!strcmp(mode,"truncated-request"))--n;
    if(!strcmp(mode,"bad-features")){
        size_t at=48+strlen("cranelift")+strlen("x86_64-pc-windows-msvc")+strlen("znver3");
        fixture_u32(out+at,129);
    }
    return n;
}
#endif
