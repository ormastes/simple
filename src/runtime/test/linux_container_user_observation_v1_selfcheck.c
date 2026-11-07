/* Actual Core-C observer fixture. Child processes are owned only by this
 * harness; the production observer must never signal, wait for or adopt them. */
#define _GNU_SOURCE
#include "runtime.h"
#include "runtime_workspace_storage_v1.h"
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <dirent.h>
#include <pthread.h>
#include <sys/stat.h>
#include <sys/wait.h>
static unsigned checks;
#define CHECK(x) do {checks++;if(!(x)){fprintf(stderr,"FAIL:%d:%s\n",__LINE__,#x);abort();}} while(0)
static int64_t text_value(const char* s){return rt_string_new((const uint8_t*)s,strlen(s));}
static int fd_count(void){DIR* d=opendir("/proc/self/fd");if(!d)return -1;int n=0;while(readdir(d))n++;closedir(d);return n;}
static int fields(int64_t value,char storage[6144],char* rows[21]){
    int64_t n=rt_string_len(value);if(n<=0||n>=6144)return 0;
    memcpy(storage,rt_string_data(value),(size_t)n);storage[n]=0;
    char* p=storage;int count=0;
    while(*p){if(count==21)return 0;rows[count++]=p;char* e=strchr(p,'\n');if(!e)return 0;*e=0;p=e+1;}
    return count;
}
typedef struct {int64_t token,binding,result;} CrossThread;
static void* cross_thread(void* pointer){CrossThread* x=pointer;x->result=rt_string_len(rt_linux_container_user_observe_v1(x->token,x->binding));return NULL;}
int main(void){
#if defined(__linux__)
    char cgroup[4096];FILE* cg=fopen("/proc/self/cgroup","r");CHECK(cg!=NULL);
    CHECK(fgets(cgroup,sizeof(cgroup),cg)!=NULL);CHECK(fclose(cg)==0);CHECK(!strncmp(cgroup,"0::/",4));
    size_t length=strlen(cgroup);CHECK(length>5&&cgroup[length-1]=='\n');cgroup[length-1]=0;
    const char* path=cgroup+3;CHECK(strcmp(path,"/")!=0);
    int baseline=fd_count();CHECK(baseline>0);
    int gate[2],ready[2];CHECK(pipe(gate)==0);CHECK(pipe(ready)==0);
    pid_t child=fork();CHECK(child>=0);
    if(!child){close(gate[1]);close(ready[0]);char c='R';if(write(ready[1],&c,1)!=1)_exit(98);
        if(read(gate[0],&c,1)!=1)_exit(99);_exit(17);}
    close(gate[0]);close(ready[1]);char signal=0;CHECK(read(ready[0],&signal,1)==1&&signal=='R');close(ready[0]);
    const char* digest="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    int64_t binding=text_value(digest),wrong=text_value("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb");
    int live_fds=fd_count();
    CHECK(rt_linux_container_user_open_v1(-1,text_value(path),binding)==-EINVAL);
    CHECK(rt_linux_container_user_open_v1(child,text_value("/"),binding)==-EINVAL);
    CHECK(rt_linux_container_user_open_v1(child,text_value("/not-this-cgroup"),binding)<0);
    const uint8_t embedded[]={'/','b','a','d',0,'/','x'};
    CHECK(rt_linux_container_user_open_v1(child,rt_string_new(embedded,sizeof(embedded)),binding)==-EINVAL);
    CHECK(rt_linux_container_user_open_v1(child,text_value(path),text_value("bad"))==-EINVAL);
    CHECK(fd_count()==live_fds);
    int64_t token=rt_linux_container_user_open_v1(child,text_value(path),binding);CHECK(token>0);
    char record[6144];char* row[21];CHECK(fields(rt_linux_container_user_observe_v1(token,binding),record,row)==21);
    CHECK(strcmp(row[0],"linux-container-user-native-v1")==0);CHECK(strtoll(row[1],NULL,10)==token);
    CHECK(strtol(row[2],NULL,10)==child);CHECK(strtoull(row[3],NULL,10)>0);
    CHECK(strtoul(row[4],NULL,10)==geteuid());CHECK(strtoul(row[5],NULL,10)==getegid());
    CHECK(strtoul(row[6],NULL,10)==geteuid());CHECK(strtoul(row[7],NULL,10)==getegid());
    CHECK(strtoul(row[8],NULL,10)==geteuid());CHECK(strtoul(row[9],NULL,10)==getegid());
    CHECK(strtoul(row[10],NULL,10)==geteuid());CHECK(strtoul(row[11],NULL,10)==getegid());
    struct stat ns;CHECK(stat("/proc/self/ns/user",&ns)==0);
    CHECK(strtoull(row[12],NULL,10)==(unsigned long long)ns.st_dev);CHECK(strtoull(row[13],NULL,10)==(unsigned long long)ns.st_ino);
    CHECK(strtoull(row[14],NULL,10)==(unsigned long long)ns.st_dev);CHECK(strtoull(row[15],NULL,10)==(unsigned long long)ns.st_ino);
    CHECK(strcmp(row[16],path)==0);CHECK(strlen(row[17])==64&&strlen(row[18])==64);CHECK(strtoll(row[19],NULL,10)>0);CHECK(strcmp(row[20],digest)==0);
    CHECK(rt_string_len(rt_linux_container_user_observe_v1(token,wrong))==0);
    CHECK(rt_linux_container_user_close_v1(token,wrong)==-ESTALE);
    CHECK(rt_workspace_storage_release_if_absent_v1(token)==-ESTALE);
    CHECK(rt_workspace_storage_forget_released_v1(token)==-ESTALE);
    CHECK(rt_string_len(rt_workspace_storage_observe_v1(token))==0);
    CrossThread other={token,binding,-1};pthread_t thread;CHECK(pthread_create(&thread,NULL,cross_thread,&other)==0);
    CHECK(pthread_join(thread,NULL)==0);CHECK(other.result==0);
    CHECK(rt_string_len(rt_linux_container_user_observe_v1(token,binding))>0);
    CHECK(rt_linux_container_user_close_v1(token,binding)==0);
    int status=0;CHECK(waitpid(child,&status,WNOHANG)==0); /* close did not kill/reap */
    int64_t next=rt_linux_container_user_open_v1(child,text_value(path),binding);CHECK(next>token);
    CHECK(rt_linux_container_user_close_v1(token,binding)==-ESTALE);
    CHECK(rt_string_len(rt_linux_container_user_observe_v1(next,binding))>0);
    CHECK(write(gate[1],"X",1)==1);close(gate[1]);
    int dead=0;for(int i=0;i<1000;i++){if(rt_string_len(rt_linux_container_user_observe_v1(next,binding))==0){dead=1;break;}usleep(1000);}
    CHECK(dead);CHECK(waitpid(child,&status,0)==child);CHECK(WIFEXITED(status)&&WEXITSTATUS(status)==17);
    CHECK(rt_linux_container_user_close_v1(next,binding)==0);CHECK(rt_linux_container_user_close_v1(next,binding)==-ESTALE);
    CHECK(fd_count()==baseline);
    printf("PASS real Linux user observer: %u checks; pidfd lifetime, namespace facts, kind/binding/generation, no reap, no FD leak\n",checks);return 0;
#else
    fputs("UNSUPPORTED: Linux native observer fixture requires Linux\n",stderr);return 77;
#endif
}
