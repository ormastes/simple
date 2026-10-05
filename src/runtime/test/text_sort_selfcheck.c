#include "runtime.h"
#include <stdio.h>
#include <string.h>
extern bool rt_array_sort(int64_t);
static unsigned checks;
#define CHECK(x) do { ++checks; if(!(x)){fprintf(stderr,"FAIL line=%d check=%u\n",__LINE__,checks);return 1;} }while(0)
int main(void){
 const unsigned char *texts[]={(const unsigned char*)"pear",(const unsigned char*)"a\0z",(const unsigned char*)"ab",(const unsigned char*)"a",(const unsigned char*)"B",(const unsigned char*)"\xc3\xa9",(const unsigned char*)"",(const unsigned char*)"\xf0\x9f\x98\x80"};
 const int lens[]={4,3,2,1,1,2,0,4}, order[]={6,4,3,1,2,0,5,7};
 int64_t values[8]; SplArray *a=rt_array_new(8); CHECK(a);
 for(int i=0;i<8;i++){values[i]=rt_string_new(texts[i],lens[i]);CHECK(rt_array_push(a,values[i]));}
 SplArray *b=(SplArray*)(uintptr_t)rt_array_sorted((int64_t)(uintptr_t)a);CHECK(b&&b!=a&&rt_array_len(b)==8);
 for(int i=0;i<8;i++){int64_t v=rt_array_get(b,i);CHECK(rt_string_len(v)==lens[order[i]]);CHECK(!memcmp(rt_string_data(v),texts[order[i]],lens[order[i]]));CHECK(rt_array_get(a,i)==values[i]);}
 CHECK(rt_array_sort((int64_t)(uintptr_t)a));for(int i=0;i<8;i++) CHECK(rt_array_get(a,i)==values[order[i]]);
 int64_t other[]={rt_value_int(7),rt_value_float(2.5),rt_value_bool(true),rt_value_nil()};
 for(int t=0;t<4;t++)for(int rev=0;rev<2;rev++){int64_t pair[]={rev?other[t]:values[0],rev?values[0]:other[t]};a=rt_array_new(2);CHECK(a);CHECK(rt_array_push(a,pair[0]));CHECK(rt_array_push(a,pair[1]));b=(SplArray*)(uintptr_t)rt_array_sorted((int64_t)(uintptr_t)a);CHECK(b);CHECK(rt_array_get(b,0)==pair[0]);CHECK(rt_array_get(b,1)==pair[1]);}
 a=rt_array_new(2);CHECK(rt_array_push(a,rt_value_float(-100.0)));CHECK(rt_array_push(a,rt_value_int(100)));b=(SplArray*)(uintptr_t)rt_array_sorted((int64_t)(uintptr_t)a);CHECK(rt_array_get(b,0)==rt_value_int(100));CHECK(rt_value_as_float(rt_array_get(b,1))==-100.0);
 printf("PASS text_sort_native checks=%u prefix=1 utf8=1 empty=1 embedded_nul=1 mixed_pairs=8 input_preservation=1\n",checks);return 0;
}