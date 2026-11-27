/* Test-only GNU ld --wrap fault injection. Each selected EVP call reports one
 * failure. All unselected calls delegate to the real linked OpenSSL library.
 * These tests prove wrapper error/cleanup behavior, not cryptographic success. */
enum fault_op { F_NONE, F_NEW, F_CTRL, F_ENC_INIT, F_ENC_UPDATE, F_ENC_FINAL,
                F_DEC_INIT, F_DEC_UPDATE };
static enum fault_op selected_fault;
static unsigned selected_call, seen_calls, injected_failures;
static unsigned ctx_created, ctx_freed, owner_allocated, owner_freed;
static int fail_selected(enum fault_op op) {
    if(op!=selected_fault) return 0;
    if(++seen_calls!=selected_call) return 0;
    injected_failures++;
    return 1;
}
static void* owner_test_malloc(size_t n) {
    void* p=malloc(n); if(p) owner_allocated++; return p;
}
static void owner_test_free(void* p) {
    if(p) owner_freed++;
    free(p);
}
EVP_CIPHER_CTX* __real_EVP_CIPHER_CTX_new(void);
void __real_EVP_CIPHER_CTX_free(EVP_CIPHER_CTX* ctx);
int __real_EVP_CIPHER_CTX_ctrl(EVP_CIPHER_CTX* ctx,int type,int arg,void* ptr);
EVP_CIPHER_CTX* __wrap_EVP_CIPHER_CTX_new(void) {
    if(fail_selected(F_NEW)) return NULL;
    EVP_CIPHER_CTX* ctx=__real_EVP_CIPHER_CTX_new();
    if(ctx) ctx_created++;
    return ctx;
}
void __wrap_EVP_CIPHER_CTX_free(EVP_CIPHER_CTX* ctx) {
    if(ctx) ctx_freed++;
    __real_EVP_CIPHER_CTX_free(ctx);
}
int __wrap_EVP_CIPHER_CTX_ctrl(EVP_CIPHER_CTX* ctx,int type,int arg,void* ptr) {
    if(fail_selected(F_CTRL)) return 0;
    return __real_EVP_CIPHER_CTX_ctrl(ctx,type,arg,ptr);
}
#define WRAP_INIT(name,op) \
int __real_##name(EVP_CIPHER_CTX*,const EVP_CIPHER*,ENGINE*,const unsigned char*,const unsigned char*); \
int __wrap_##name(EVP_CIPHER_CTX* ctx,const EVP_CIPHER* type,ENGINE* engine,const unsigned char* key,const unsigned char* iv) { \
    if(fail_selected(op)) return 0; \
    return __real_##name(ctx,type,engine,key,iv); \
}
WRAP_INIT(EVP_EncryptInit_ex,F_ENC_INIT)
WRAP_INIT(EVP_DecryptInit_ex,F_DEC_INIT)
#define WRAP_UPDATE(name,op) \
int __real_##name(EVP_CIPHER_CTX*,unsigned char*,int*,const unsigned char*,int); \
int __wrap_##name(EVP_CIPHER_CTX* ctx,unsigned char* out,int* outl,const unsigned char* in,int inl) { \
    if(fail_selected(op)) return 0; \
    return __real_##name(ctx,out,outl,in,inl); \
}
WRAP_UPDATE(EVP_EncryptUpdate,F_ENC_UPDATE)
WRAP_UPDATE(EVP_DecryptUpdate,F_DEC_UPDATE)
int __real_EVP_EncryptFinal_ex(EVP_CIPHER_CTX*,unsigned char*,int*);
int __wrap_EVP_EncryptFinal_ex(EVP_CIPHER_CTX* ctx,unsigned char* out,int* outl) {
    if(fail_selected(F_ENC_FINAL)) return 0;
    return __real_EVP_EncryptFinal_ex(ctx,out,outl);
}
static int test_evp_failures(void) {
    const struct { const char* name; int decrypt; enum fault_op op; unsigned nth; } cases[]={
        {"encrypt/context allocation",0,F_NEW,1},
        {"encrypt/initial init",0,F_ENC_INIT,1},
        {"encrypt/IV control",0,F_CTRL,1},
        {"encrypt/key init",0,F_ENC_INIT,2},
        {"encrypt/AAD update",0,F_ENC_UPDATE,1},
        {"encrypt/data update",0,F_ENC_UPDATE,2},
        {"encrypt/final",0,F_ENC_FINAL,1},
        {"encrypt/tag control",0,F_CTRL,2},
        {"decrypt/context allocation",1,F_NEW,1},
        {"decrypt/initial init",1,F_DEC_INIT,1},
        {"decrypt/IV control",1,F_CTRL,1},
        {"decrypt/key init",1,F_DEC_INIT,2},
        {"decrypt/AAD update",1,F_DEC_UPDATE,1},
        {"decrypt/tag control",1,F_CTRL,2},
        {"decrypt/data update",1,F_DEC_UPDATE,2}
    };
    char key[16]={0},iv[12]={0},pt[16]={0},ct[32]; int64_t n;
    /* Generate a genuine authenticated input before enabling any fault. */
    const char* valid=rt_aes_gcm_encrypt_with_len(key,16,iv,12,pt,16,"aad",3,&n);
    CHECK(valid && n==32);
    memcpy(ct,valid,32); owner_test_free((void*)valid);
    for(unsigned i=0;i<sizeof(cases)/sizeof(cases[0]);i++) {
        unsigned created_before=ctx_created,freed_before=ctx_freed;
        unsigned allocated_before=owner_allocated,released_before=owner_freed;
        selected_fault=cases[i].op; selected_call=cases[i].nth;
        seen_calls=0; injected_failures=0; n=123;
        const char* result=cases[i].decrypt
            ? rt_aes_gcm_decrypt_with_len(key,16,iv,12,ct,32,"aad",3,&n)
            : rt_aes_gcm_encrypt_with_len(key,16,iv,12,pt,16,"aad",3,&n);
        selected_fault=F_NONE;
        CHECK(injected_failures==1);
        CHECK(n==0);
        CHECK(result && result[0]==0);
        CHECK(ctx_created-created_before==ctx_freed-freed_before);
        CHECK(owner_allocated-allocated_before==owner_freed-released_before);
        free((void*)result);
        printf("INJECTED EVP failure PASS: %s; context/buffer balances verified\n",cases[i].name);
    }
    return 0;
}
