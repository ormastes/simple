#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef _WIN32
#include <windows.h>
#define pause_ms(n) Sleep(n)
#else
#include <unistd.h>
#define pause_ms(n) usleep((n)*1000)
#endif
int main(int argc,char**argv) {
    /* Private negative controls, never accepted as the positive GDB backend. */
    if (strstr(argv[0],"forbidden")) {
        const char* marker=getenv("MCPGDB_TEST_TRAP_MARKER");
        FILE* out=marker?fopen(marker,"wb"):NULL;
        if(out){fputs("unexpected source launcher invocation",out);fclose(out);}
        return 97;
    }
    if (strstr(argv[0],"resident_")) {
        char line[65536];int continues=0;
        fputs("(gdb) \n",stdout);fflush(stdout);
        while(fgets(line,sizeof(line),stdin)) {
            long long token=strtoll(line,NULL,10);
            if(strstr(argv[0],"resident_wrongtoken")) { printf("%lld^done\n",token+1);fflush(stdout);continue; }
            if(strstr(argv[0],"resident_deadline")) { pause_ms(10000);continue; }
            if(strstr(argv[0],"resident_eof")) { printf("%lld^done",token);fflush(stdout);return 7; }
            if(strstr(line,"-gdb-exit")) { printf("%lld^exit\n",token);fflush(stdout);return 0; }
            if(strstr(argv[0],"resident_error") && strstr(line,"-exec-continue")) {
                printf("%lld^error,msg=\"deliberate MI error control\"\n(gdb) \n",token);fflush(stdout);continue;
            }
            if(strstr(argv[0],"resident_order") && strstr(line,"-exec-continue")) {
                continues++;
                if(continues==1) fputs("*stopped,reason=\"end-stepping-range\",frame={func=\"control_fixture\"}\n",stdout);
                printf("%lld^running\n",token);fflush(stdout);continue;
            }
            if(strstr(argv[0],"resident_order") && strstr(line,"-exec-interrupt")) {
                printf("%lld^done\n*stopped,reason=\"signal-received\",frame={func=\"control_fixture\"}\n",token);fflush(stdout);continue;
            }
            if(strstr(argv[0],"resident_fragmented")) {
                printf("%lld^",token);fflush(stdout);pause_ms(30);
                fputs("done\n~\"",stdout);fputc(0xc3,stdout);fflush(stdout);pause_ms(30);
                fputc(0xa9,stdout);fputs("\"\n(gdb) \n",stdout);fflush(stdout);continue;
            }
            printf("%lld^done\n(gdb) \n",token);fflush(stdout);
        }
        return 0;
    }
    if (strstr(argv[0],"fake_tool_error")) {
        fputs("{\"jsonrpc\":\"2.0\",\"id\":\"1\",\"result\":{\"content\":[{\"type\":\"text\",\"text\":\"deliberate child isError control\"}],\"isError\":true}}\n",stdout);
        return 0;
    }
    if (strstr(argv[0],"fakegdb_nonzero")) {
        fputs("GNU gdb negative control 18.1\n1^done\n2^done\n3^exit\n",stdout);
        return 7;
    }
    if (strstr(argv[0],"fakegdb_timeout")) {
        fputs("GNU gdb negative control 18.1\n1^done\n2^done\n3^exit\n",stdout);
        fflush(stdout);pause_ms(10000);return 0;
    }
    if (strstr(argv[0],"fakegdb_malformed")) {
        fputs("GNU gdb negative control without command receipts\n",stdout);return 0;
    }
    if (argc != 2) return 99;
    if (!strcmp(argv[1],"hang")) { fputs("pending",stdout);fflush(stdout);pause_ms(10000);return 0; }
    if (!strcmp(argv[1],"tail")) { for(int i=0;i<200000;i++)putchar('x');fputs("TAIL",stdout);return 0; }
    if (!strcmp(argv[1],"exit7")) { fputs("nonzero",stdout);return 7; }
    if (!strcmp(argv[1],"exit259")) { fputs("not-STILL_ACTIVE",stdout);return 259; }
    if (!strcmp(argv[1],"exit0")) { fputs("zero",stdout);return 0; }
    return 98;
}
