/* V3 contract witness using actual CoreC owner implementations. This test does
 * not manufacture successful cgroup enforcement from regular files: the file
 * cases below only exercise exact cpu.max text decoding. Explicit host-supplied
 * delegated/broker fixtures are separately needed for cgroup admission. */
#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE
#endif
#include "../runtime_process_owned.c"
#include <assert.h>
#if !defined(__linux__) || defined(RT_PROCESS_OWNED_CORE_ONLY)
int main(void){return 77;}
#else
static const char *policy="cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc";
static SplArray *profile_words(const int64_t values[12]) {
    SplArray *a=rt_array_new(12);assert(a);
    for(int i=0;i<12;i++)assert(rt_array_push(a,rt_value_int(values[i])));
    return a;
}
int main(void) {
    alarm(10);
    int64_t values[12]={25,2500,100000,11,22,3,250000,1000000,250,67108864,134217728,1};
    /* Counted length is exact; no path guessing or fake cgroup success. */
    const char *path="/test/delegated/broker";
    SplArray *a=profile_words(values);RtGroupStreamProfileV3 parsed;
    assert(rt_lg_profile_parse_v3(path,strlen(path),policy,64,a,&parsed));
    rt_array_free(a);
    a=rt_array_new(11);assert(a);
    for(int i=0;i<11;i++)assert(rt_array_push(a,rt_value_int(values[i])));
    assert(!rt_lg_profile_parse_v3(path,strlen(path),policy,64,a,&parsed));rt_array_free(a);
    a=profile_words(values);
    const char nul_path[]="/test/delegated/broker\0hidden";
    assert(!rt_lg_profile_parse_v3(nul_path,sizeof(nul_path)-1,policy,64,a,&parsed));
    assert(!rt_lg_profile_parse_v3(path,strlen(path),"not-a-digest",12,a,&parsed));
    rt_array_free(a);
    values[1]=2499;a=profile_words(values);
    assert(!rt_lg_profile_parse_v3(path,strlen(path),policy,64,a,&parsed));rt_array_free(a);
    values[1]=2500;
    /* Exact reservation boundary accepts, one extra microsecond refuses. */
    assert(rt_lg_profile_parse_v3(path,strlen(path),policy,64,(a=profile_words(values)),&parsed));rt_array_free(a);
    values[6]=250001;a=profile_words(values);
    assert(!rt_lg_profile_parse_v3(path,strlen(path),policy,64,a,&parsed));rt_array_free(a);
    values[6]=250000;
    for(int64_t millis=1;millis<=10;millis++) {
        values[0]=millis;values[1]=millis*(millis<10?1000:100);values[2]=millis<10?1000000:100000;
        a=profile_words(values);assert(rt_lg_profile_parse_v3(path,strlen(path),policy,64,a,&parsed));rt_array_free(a);
    }
    values[0]=INT64_MAX;values[1]=1000;values[2]=100000;
    a=profile_words(values);assert(!rt_lg_profile_parse_v3(path,strlen(path),policy,64,a,&parsed));rt_array_free(a);
    values[0]=25;values[1]=2500;values[2]=100000;
    values[6]=250001;
    a=profile_words(values);assert(!rt_lg_profile_parse_v3(path,strlen(path),policy,64,a,&parsed));rt_array_free(a);
    values[6]=250000;values[11]=2;
    a=profile_words(values);assert(!rt_lg_profile_parse_v3(path,strlen(path),policy,64,a,&parsed));rt_array_free(a);
    values[11]=1;values[9]=values[10]+1;
    a=profile_words(values);assert(!rt_lg_profile_parse_v3(path,strlen(path),policy,64,a,&parsed));rt_array_free(a);
    values[9]=67108864;
    a=rt_array_new(12);assert(a);
    for(int i=0;i<12;i++)assert(rt_array_push(a,i==0?rt_string_new((const uint8_t*)"25",2):rt_value_int(values[i])));
    assert(!rt_lg_profile_parse_v3(path,strlen(path),policy,64,a,&parsed));rt_array_free(a);
    a=profile_words(values);
    assert(rt_linux_group_stream_admit_profiled_v3("/",1,path,strlen(path),policy,64,a)!=0);
    assert(rt_linux_group_stream_verify_broker_profiled_v3("/",1,path,strlen(path),policy,64,a)!=0);
    assert(!rt_linux_group.active&&!rt_lg_delegation.active);
    rt_array_free(a);
    char temporary[]="/tmp/simple-cpu-profile-v3-XXXXXX";
    char *directory=mkdtemp(temporary);assert(directory);
    int root=open(directory,O_RDONLY|O_DIRECTORY|O_CLOEXEC);assert(root>=0);
    int fd=openat(root,"cpu.max",O_WRONLY|O_CREAT|O_EXCL|O_CLOEXEC,0600);assert(fd>=0);
    assert(write(fd,"2500 100000\n",12)==12);close(fd);
    assert(rt_lg_cpu_readback_v3(root,2500,100000));
    assert(!rt_lg_cpu_readback_v3(root,2501,100000));
    fd=openat(root,"cpu.max",O_WRONLY|O_TRUNC|O_CLOEXEC);assert(fd>=0);
    assert(write(fd,"max 100000\n",11)==11);close(fd);
    assert(!rt_lg_cpu_readback_v3(root,2500,100000));
    assert(unlinkat(root,"cpu.max",0)==0);close(root);assert(rmdir(directory)==0);
    puts("PASS V3 typed-policy rejection and exact readback parsing; actual cgroup enforcement NOT_RUN");
    return 0;
}
#endif
