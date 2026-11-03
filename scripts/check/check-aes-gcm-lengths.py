from pathlib import Path
import argparse, hashlib, subprocess
p=argparse.ArgumentParser()
p.add_argument('--root',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
p.add_argument('--cc',default='cc')
p.add_argument('--openssl',action='store_true')
p.add_argument('--inject-evp-failures',action='store_true',help='Test-only linker EVP failures; requires --openssl')
p.add_argument('--emit-only',action='store_true',help='Write the exact owner translation unit without building or running')
a=p.parse_args()
if a.inject_evp_failures and not a.openssl:
    p.error('--inject-evp-failures requires --openssl')
a.output.mkdir(parents=True,exist_ok=True)
src=(a.root/'src/runtime/runtime.c').read_text()
if a.openssl:
    start=src.index('/* ---- rt_aes_gcm_encrypt_with_len: binary-safe AES-128-GCM encrypt (OpenSSL) ---- */')
    end=src.index('#else /* !SPL_HAVE_OPENSSL',start)
else:
    start=src.index('static const uint8_t aes_sbox[256]')
    end=src.index('#endif /* SPL_HAVE_OPENSSL */',start)
# Exact production slice: allocator macros only adapt the standalone test host.
prefix='''#include <stdint.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define SPL_MALLOC(n,t) malloc(n)
#define SPL_FREE(p) free(p)
static char* test_strdup(const char* s) { size_t n=strlen(s)+1; char* p=malloc(n); if(p) memcpy(p,s,n); return p; }
#define SPL_STRDUP(s,t) test_strdup(s)
'''
if a.openssl: prefix += '#define SPL_HAVE_OPENSSL 1\n#include <openssl/evp.h>\n'
if a.inject_evp_failures:
    prefix += '''#define TEST_EVP_FAILURES 1
static void* owner_test_malloc(size_t n);
static void owner_test_free(void* p);
static int test_evp_failures(void);
#undef SPL_MALLOC
#undef SPL_FREE
#define SPL_MALLOC(n,t) owner_test_malloc(n)
#define SPL_FREE(p) owner_test_free(p)
'''
fixture=a.root/'test/01_unit/runtime/aes_gcm_lengths_test.c'
unit=a.output/'aes_gcm_owner.c'
suffix=''
if a.inject_evp_failures:
    suffix=(a.root/'test/01_unit/runtime/aes_gcm_evp_faults_test.c').read_text()
unit.write_text(prefix+src[start:end]+'\n'+fixture.read_text()+'\n'+suffix)
if a.emit_only:
    print(str(unit))
    raise SystemExit(0)
exe=a.output/'aes_gcm_lengths_test.exe'
cmd=[a.cc,'-std=c11','-O2',str(unit),'-o',str(exe)]
if a.openssl: cmd += ['-lcrypto']
if a.inject_evp_failures:
    symbols=['EVP_CIPHER_CTX_new','EVP_CIPHER_CTX_free','EVP_CIPHER_CTX_ctrl',
             'EVP_EncryptInit_ex','EVP_EncryptUpdate','EVP_EncryptFinal_ex',
             'EVP_DecryptInit_ex','EVP_DecryptUpdate']
    cmd += ['-Wl,--wrap='+symbol for symbol in symbols]
    print('fault_injection=selected EVP failure only; all other calls use real OpenSSL',flush=True)
print('source_sha256='+hashlib.sha256((a.root/'src/runtime/runtime.c').read_bytes()).hexdigest(),flush=True)
print('provider='+('OpenSSL' if a.openssl else 'scalar fallback'),flush=True)
subprocess.run(cmd,check=True,timeout=60)
print('exe_sha256='+hashlib.sha256(exe.read_bytes()).hexdigest(),flush=True)
subprocess.run([str(exe)],check=True,timeout=15)
