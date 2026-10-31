/* Concurrent same-path writers of rt_file_atomic_write never expose a partial
 * file, a new file takes the umask, a replaced file keeps its mode, and the
 * byte twin keeps NUL and non-UTF-8 bytes.
 *   cc -c -std=gnu11 -DSIMPLE_CORE_C_STANDALONE=1 -DSIMPLE_RUNTIME_MEMORY_OWNER=1 \
 *      -DSIMPLE_RUNTIME_PROCESS_OWNED_STRING_FREE=1 -Isrc/runtime \
 *      -Isrc/runtime/platform src/runtime/runtime_native.c -o rn.o
 *   cc -std=gnu11 THIS_FILE rn.o -lpthread -lm -Wl,-dead_strip -o check
 *   ./check /tmp/some_new_path
 * POSIX only; the Windows rename retry has no coverage here. */
#include <pthread.h>
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
#include <stdint.h>
#include <stdlib.h>
#include <unistd.h>
#include <dirent.h>
extern int64_t rt_file_atomic_write(int64_t,int64_t);
extern int8_t rt_file_atomic_write_bytes_array(int64_t,int64_t);
extern int64_t rt_string_new(const uint8_t*,uint64_t);
extern int64_t rt_bytes_from_raw(int64_t,int64_t);
#define TV(s) rt_string_new((const uint8_t*)(s),strlen(s))
static const char*P; static int64_t pv; static volatile int stop; static int64_t vals[4]; static int lens[4]={1000,70000,3,300000};
static void* w(void*a){long i=(long)a;for(int k=0;k<1500;k++) if(!rt_file_atomic_write(pv,vals[i])){puts("WRITE FAIL");exit(1);}return 0;}
static void* r(void*a){static char b[400000];long n=0;while(!stop){FILE*f=fopen(P,"rb");if(!f)continue;size_t g=fread(b,1,sizeof b,f);fclose(f);n++;
 int ok=0;for(int i=0;i<4;i++)if((int)g==lens[i]){ok=1;for(size_t j=0;j<g;j++)if(b[j]!='a'+i)ok=0;}
 if(!ok){printf("PARTIAL len=%zu\n",g);exit(2);}}printf("reads=%ld\n",n);return 0;}
int main(int c,char**v){P=v[1];pv=TV(P);umask(022);
 for(int i=0;i<4;i++){char*s=malloc(lens[i]+1);memset(s,'a'+i,lens[i]);s[lens[i]]=0;vals[i]=TV(s);}
 rt_file_atomic_write(pv,vals[2]);
 struct stat st;stat(P,&st);printf("newmode=%o\n",st.st_mode&0777);if((st.st_mode&0777)!=0644)return 3;
 chmod(P,0755);pthread_t t[5];for(long i=0;i<4;i++)pthread_create(&t[i],0,w,(void*)i);pthread_create(&t[4],0,r,0);
 for(int i=0;i<4;i++)pthread_join(t[i],0);stop=1;pthread_join(t[4],0);
 stat(P,&st);printf("keptmode=%o\n",st.st_mode&0777);if((st.st_mode&0777)!=0755)return 4;
 {static const unsigned char raw[5]={0,0xff,'x',0,0x80};unsigned char b[8];
  if(rt_file_atomic_write_bytes_array(pv,rt_bytes_from_raw((int64_t)(intptr_t)raw,5))!=1)return 5;
  FILE*f=fopen(P,"rb");size_t g=fread(b,1,8,f);fclose(f);if(g!=5||memcmp(b,raw,5))return 6;}
 puts("OK");return 0;}
#include <sys/stat.h>
char* spl_strdup(const char*s){return strdup(s);}
_Bool rt_is_dir(const char*p){struct stat s;return stat(p,&s)==0&&S_ISDIR(s.st_mode);}
