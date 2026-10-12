#include <windows.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
extern int64_t rt_string_new(const uint8_t *, uint64_t);
extern int64_t rt_term_write(int64_t);
extern void term_test_control(unsigned mode);
static DWORD WINAPI queued_writer(void *unused) {
    (void)unused;
    for (unsigned i=0;i<100;i++) if (fwrite("QQ\n",1,3,stdout)!=3) return 1;
    return 0;
}
int main(int argc,char **argv) {
    if(argc!=2)return 2;
    const uint8_t payload[]={'A',0,0xc3,0xa9,'\n','\r','\n','Z'};
    int64_t text=rt_string_new(payload,sizeof payload);
    if(!strcmp(argv[1],"short")) {term_test_control(1);return rt_term_write(text)==8?0:10;}
    if(!strcmp(argv[1],"zero")) {term_test_control(2);return rt_term_write(text)==0?0:11;}
    if(!strcmp(argv[1],"error")) {term_test_control(3);return rt_term_write(text)==0?0:12;}
    if(!strcmp(argv[1],"partial-error")) {term_test_control(4);return rt_term_write(text)==2?0:13;}
    if(!strcmp(argv[1],"held")) {
        if(rt_term_write(text)!=8)return 14;
        /* Parent must see raw8 bytes before allowing process exit. */
        char byte;DWORD read=0;
        if(!ReadFile(GetStdHandle(STD_INPUT_HANDLE),&byte,1,&read,NULL)||read!=1||byte!='!')return 15;
        return 0;
    }
    if(!strcmp(argv[1],"concurrent")) {
        HANDLE child=CreateThread(NULL,0,queued_writer,NULL,0,NULL);if(!child)return 16;
        for(unsigned i=0;i<100;i++)if(rt_term_write(rt_string_new((const uint8_t*)"RR\n",3))!=3)return 17;
        if(WaitForSingleObject(child,10000)!=WAIT_OBJECT_0)return 18;
        DWORD code=1;GetExitCodeThread(child,&code);CloseHandle(child);
        return code==0&&fflush(stdout)==0?0:19;
    }
    return 3;
}
