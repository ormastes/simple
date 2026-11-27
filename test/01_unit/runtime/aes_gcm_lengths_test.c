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
    /* Legacy string entrypoints reject each missing required pointer. Their
     * strlen contract intentionally cannot carry binary ciphertext. */
    const char* text_key="0123456789abcdef";
    const char* text_iv="0123456789ab";
    for(int missing=0;missing<3;missing++) {
        const char* k=missing==0 ? NULL : text_key;
        const char* v=missing==1 ? NULL : text_iv;
        const char* p=missing==2 ? NULL : "sample";
        out=rt_aes_gcm_encrypt(k,v,p,NULL);
        CHECK(out && out[0]==0); free((void*)out);
        out=rt_aes_gcm_decrypt(k,v,p,NULL);
        CHECK(out && out[0]==0); free((void*)out);
        out=rt_aes_gcm_encrypt_with_len(k,16,v,12,p,6,NULL,0,&n);
        CHECK(empty_failure(out,n));
        out=rt_aes_gcm_decrypt_with_len(k,16,v,12,p,16,NULL,0,&n);
        CHECK(empty_failure(out,n));
    }
    for(int with_aad=0;with_aad<2;with_aad++) {
        const char* a=with_aad ? "aad" : NULL;
        int64_t expected_len;
        const char* expected=rt_aes_gcm_encrypt_with_len(text_key,16,text_iv,12,"sample",6,a,with_aad?3:0,&expected_len);
        out=rt_aes_gcm_encrypt(text_key,text_iv,"sample",a);
        CHECK(expected_len==22 && memcmp(out,expected,22)==0);
        free((void*)out); free((void*)expected);
        out=rt_aes_gcm_decrypt(text_key,text_iv,"unauthenticated!",a);
        CHECK(out && out[0]==0); free((void*)out);
    }
    out=rt_aes_gcm_decrypt_with_len(key,16,iv,12,(const char*)kat,32,NULL,0,NULL);
    CHECK(out && memcmp(out,"\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0",16)==0);
    free((void*)out);
    /* Exercise the general IV GHASH path, including a partial final block. */
    char extended_iv[60]; memset(extended_iv,0x80,sizeof(extended_iv));
    int iv_lengths[]={16,17,60};
    for(unsigned i=0;i<sizeof(iv_lengths)/sizeof(iv_lengths[0]);i++) {
        int64_t cn;
        char* ct=(char*)rt_aes_gcm_encrypt_with_len(key,16,extended_iv,iv_lengths[i],msg,33,msg,17,&cn);
        CHECK(cn==49);
        out=rt_aes_gcm_decrypt_with_len(key,16,extended_iv,iv_lengths[i],ct,cn,msg,17,&n);
        CHECK(n==33 && memcmp(out,msg,33)==0); free((void*)out);
        ct[cn-1]^=0x80;
        out=rt_aes_gcm_decrypt_with_len(key,16,extended_iv,iv_lengths[i],ct,cn,msg,17,&n);
        CHECK(empty_failure(out,n)); free(ct);
    }
#ifndef SPL_HAVE_OPENSSL
    /* Direct actual-owner helper tests reach defensive key checks and counter
     * carry without allocating a 64-GiB record. No helper is substituted. */
    uint8_t scratch[16]={0}, tag[16]={0}, counter[16]={0};
    CHECK(aes_gcm_encrypt_impl((const uint8_t*)key,15,(const uint8_t*)iv,12,scratch,0,scratch,0,scratch,tag)==-1);
    CHECK(aes_gcm_decrypt_impl((const uint8_t*)key,15,(const uint8_t*)iv,12,scratch,0,scratch,0,tag,scratch)==-1);
    memset(counter+12,0xff,4); counter[0]=0x7f;
    gcm_inc32(counter);
    CHECK(counter[0]==0x7f && counter[12]==0 && counter[13]==0 && counter[14]==0 && counter[15]==0);
    counter[14]=0x7f; counter[15]=0xff;
    gcm_inc32(counter);
    CHECK(counter[14]==0x80 && counter[15]==0);
    /* RSA's unsupported fallback is included by the contiguous production
     * slice. Assert its error contract without claiming RSA crypto coverage. */
    out=rt_rsa_decrypt_with_len("bad",3,"bad",3,&n);
    CHECK(empty_failure(out,n));
    out=rt_rsa_decrypt_with_len("bad",3,"bad",3,NULL);
    CHECK(out && out[0]==0); free((void*)out);
    out=rt_rsa_decrypt("bad","bad");
    CHECK(out && out[0]==0); free((void*)out);
#endif
#ifdef TEST_EVP_FAILURES
    CHECK(test_evp_failures()==0);
#endif
    printf("PASS %u AES-GCM assertions\n",checks); return 0;
}
