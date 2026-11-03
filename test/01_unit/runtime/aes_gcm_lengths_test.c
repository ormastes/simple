/* NIST GCM examples, cases 1 and 2; matching vectors also live in
 * src/compiler_rust/runtime/src/value/aes.rs. Tests invoke the actual C owner.
 * Zero key/96-bit IV: empty tag 58e2...; 16-byte ciphertext 0388... . */
static unsigned checks;
#define CHECK(c) do { checks++; if (!(c)) { fprintf(stderr,"FAIL line %d: %s\n",__LINE__,#c); return 1; } } while(0)
static int empty_failure(const char* out, int64_t len) {
    int ok=out && len==0 && out[0]==0; free((void*)out); return ok;
}
int main(void) {
    char key[16]={0}, iv[12]={0}, msg[64]={0}; int64_t n;
    const unsigned char tag0[16]={0x58,0xe2,0xfc,0xce,0xfa,0x7e,0x30,0x61,0x36,0x7f,0x1d,0x57,0xa4,0xe7,0x45,0x5a};
    const unsigned char kat[32]={0x03,0x88,0xda,0xce,0x60,0xb6,0xa3,0x92,0xf3,0x28,0xc2,0xb9,0x71,0xb2,0xfe,0x78,0xab,0x6e,0x47,0xd4,0x2c,0xec,0x13,0xbd,0xf5,0x3a,0x67,0xb2,0x12,0x57,0xbd,0xdf};
    const char* out=rt_aes_gcm_encrypt_with_len(key,16,iv,12,msg,0,NULL,0,&n);
    CHECK(n==16 && memcmp(out,tag0,16)==0); free((void*)out);
    out=rt_aes_gcm_encrypt_with_len(key,16,iv,12,msg,16,NULL,0,&n);
    CHECK(n==32 && memcmp(out,kat,32)==0); free((void*)out);
    out=rt_aes_gcm_decrypt_with_len(key,16,iv,12,(const char*)kat,32,NULL,0,&n);
    CHECK(n==16 && memcmp(out,msg,16)==0); free((void*)out);
    out=rt_aes_gcm_decrypt_with_len(key,16,iv,12,(const char*)tag0,16,NULL,0,&n);
    CHECK(n==0 && out[0]==0); free((void*)out);
    /* Exact regression: declared AAD may never silently disappear. */
    out=rt_aes_gcm_encrypt_with_len(key,16,iv,12,msg,0,NULL,1,&n);
    CHECK(empty_failure(out,n));
    out=rt_aes_gcm_decrypt_with_len(key,16,iv,12,(const char*)kat,32,NULL,1,&n);
    CHECK(empty_failure(out,n));
    int lengths[]={0,1,15,16,17,31,32,33,64};
    unsigned char binary[]={0,0x7f,0x80,0xff};
    for(int i=0;i<64;i++) msg[i]=(char)binary[i%4];
    for(unsigned i=0;i<sizeof(lengths)/sizeof(lengths[0]);i++) {
        int l=lengths[i]; int64_t cn;
        char* ct=(char*)rt_aes_gcm_encrypt_with_len(key,16,iv,12,msg,l,msg,l,&cn);
        CHECK(cn==l+16);
        out=rt_aes_gcm_decrypt_with_len(key,16,iv,12,ct,cn,msg,l,&n);
        CHECK(n==l && memcmp(out,msg,l)==0); free((void*)out);
        ct[cn-1]^=1;
        out=rt_aes_gcm_decrypt_with_len(key,16,iv,12,ct,cn,msg,l,&n);
        CHECK(empty_failure(out,n)); ct[cn-1]^=1;
        key[0]^=1;
        out=rt_aes_gcm_decrypt_with_len(key,16,iv,12,ct,cn,msg,l,&n);
        CHECK(empty_failure(out,n)); key[0]^=1;
        iv[0]^=1;
        out=rt_aes_gcm_decrypt_with_len(key,16,iv,12,ct,cn,msg,l,&n);
        CHECK(empty_failure(out,n)); iv[0]^=1;
        out=rt_aes_gcm_decrypt_with_len(key,16,iv,12,ct,cn-1,msg,l,&n);
        CHECK(empty_failure(out,n));
        if(l) {
            ct[0]^=1;
            out=rt_aes_gcm_decrypt_with_len(key,16,iv,12,ct,cn,msg,l,&n);
            CHECK(empty_failure(out,n)); ct[0]^=1;
            msg[0]^=1;
            out=rt_aes_gcm_decrypt_with_len(key,16,iv,12,ct,cn,msg,l,&n);
            CHECK(empty_failure(out,n)); msg[0]^=1;
        }
        free(ct);
    }
    int64_t bad_aad[]={-1,INT64_MIN,(int64_t)INT_MAX+1,INT64_MAX};
    for(unsigned i=0;i<sizeof(bad_aad)/sizeof(bad_aad[0]);i++) {
        out=rt_aes_gcm_encrypt_with_len(key,16,iv,12,msg,1,msg,bad_aad[i],&n);
        CHECK(empty_failure(out,n));
        out=rt_aes_gcm_decrypt_with_len(key,16,iv,12,(const char*)kat,32,msg,bad_aad[i],&n);
        CHECK(empty_failure(out,n));
    }
    int64_t bad_iv[]={-1,0,11,(int64_t)INT_MAX+1,INT64_MAX};
    for(unsigned i=0;i<sizeof(bad_iv)/sizeof(bad_iv[0]);i++) {
        out=rt_aes_gcm_encrypt_with_len(key,16,iv,bad_iv[i],msg,1,NULL,0,&n);
        CHECK(empty_failure(out,n));
        out=rt_aes_gcm_decrypt_with_len(key,16,iv,bad_iv[i],(const char*)kat,32,NULL,0,&n);
        CHECK(empty_failure(out,n));
    }
    int64_t bad_pt[]={-1,INT64_MIN,(int64_t)INT_MAX-15,INT64_MAX};
    for(unsigned i=0;i<sizeof(bad_pt)/sizeof(bad_pt[0]);i++) {
        out=rt_aes_gcm_encrypt_with_len(key,16,iv,12,msg,bad_pt[i],NULL,0,&n);
        CHECK(empty_failure(out,n));
    }
    int64_t bad_ct[]={-1,0,15,(int64_t)INT_MAX+1,INT64_MAX};
    for(unsigned i=0;i<sizeof(bad_ct)/sizeof(bad_ct[0]);i++) {
        out=rt_aes_gcm_decrypt_with_len(key,16,iv,12,(const char*)kat,bad_ct[i],NULL,0,&n);
        CHECK(empty_failure(out,n));
    }
    out=rt_aes_gcm_encrypt_with_len(key,15,iv,12,msg,1,NULL,0,&n);
    CHECK(empty_failure(out,n));
    out=rt_aes_gcm_decrypt_with_len(key,15,iv,12,(const char*)kat,32,NULL,0,&n);
    CHECK(empty_failure(out,n));
    printf("PASS %u AES-GCM assertions\n",checks); return 0;
}
