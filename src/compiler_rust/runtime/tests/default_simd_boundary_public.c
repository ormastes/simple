#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
typedef uint64_t V;
extern V rt_string_new(const unsigned char*,uint64_t);
extern int64_t rt_string_find(V,V);
extern int64_t rt_text_count_codepoints(V);
extern V rt_array_new(uint64_t);
extern bool rt_array_push(V,V),rt_array_set(V,int64_t,V),rt_array_sort(V);
extern V rt_array_get(V,int64_t),rt_value_int(int64_t),rt_value_float(double);
extern double rt_value_as_float(V);
extern V rt_numeric_dot_f64(V,V);
extern int64_t rt_numeric_active_simd_tier(void);
static uint64_t tick(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return (uint64_t)t.tv_sec*1000000000+t.tv_nsec;}
static int cmp(const void*a,const void*b){uint64_t x=*(const uint64_t*)a,y=*(const uint64_t*)b;return (x>y)-(x<y);}
int main(int argc, char **argv){
 const int smoke=argc==2 && strcmp(argv[1],"--smoke")==0; const int samples=smoke?1:30,warmups=smoke?0:3,repeats=smoke?1:16;
 const size_t n=smoke?4096:1048576,k=4096; unsigned char *bytes=malloc(n); if(!bytes)return 1; memset(bytes,'a',n);bytes[n-1]='z';
 V text=rt_string_new(bytes,n),needle=rt_string_new((const unsigned char*)"z",1),left=rt_array_new(k),right=rt_array_new(k),arr=rt_array_new(k);
 for(size_t i=0;i<k;i++){if(!rt_array_push(left,rt_value_float(1.0))||!rt_array_push(right,rt_value_float(2.0))||!rt_array_push(arr,rt_value_int(i%256)))return 2;}
 const char *names[]={"find_1MiB_x16","utf8_1MiB_x16","dot4096_x16","sort4096_u8"};
 for(int op=0;op<4;op++){
  uint64_t times[30];
  for(int sample=-warmups;sample<samples;sample++){
   if(op==3) for(size_t i=0;i<k;i++)if(!rt_array_set(arr,i,rt_value_int(255-i%256)))return 3;
   uint64_t start=tick();
   for(int repeat=0;repeat<(op==3?1:repeats);repeat++){
    if(op==0 && rt_string_find(text,needle)!=(int64_t)n-1)return 4;
    if(op==1 && rt_text_count_codepoints(text)!=(int64_t)n)return 5;
    if(op==2 && rt_value_as_float(rt_numeric_dot_f64(left,right))!=8192.0)return 6;
    if(op==3 && !rt_array_sort(arr))return 7;
   }
   uint64_t elapsed=tick()-start;
   if(op==3)for(size_t i=0;i<k;i++)if(rt_array_get(arr,i)!=rt_value_int(i/16))return 8;
   if(sample>=0)times[sample]=elapsed;
  }
  qsort(times,samples,sizeof(*times),cmp);printf("%s median_ns=%llu min_ns=%llu max_ns=%llu samples=%d warmup=%d\n",names[op],(unsigned long long)(smoke?times[0]:(times[14]+times[15])/2),(unsigned long long)times[0],(unsigned long long)times[samples-1],samples,warmups);
 }
 printf("PUBLIC_ABI_PASS numeric_execution_tier=%lld\n",(long long)rt_numeric_active_simd_tier());free(bytes);return 0;
}
