/* Windows text capture and its native tuple adapter must preserve NUL bytes. */
#include "runtime.h"
#include <windows.h>
#include <io.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern int64_t* rt_process_run_bounded_tuple(const char*, uint64_t, SplArray*, int64_t, int64_t);
extern void __simple_runtime_init(void);
static const unsigned char output[] = {'A', 0, 'B', 0};
static const unsigned char error[] = {'E', 0, 'F', 0};
static int failures;
#define CHECK(c) do { if (!(c)) { fprintf(stderr,"FAIL line %d\n",__LINE__); ++failures; } } while (0)

static void check_text(int64_t value, const unsigned char* expected, size_t size) {
    CHECK(rt_string_len(value) == (int64_t)size);
    if (rt_string_len(value) == (int64_t)size)
        CHECK(memcmp(rt_string_data(value), expected, size) == 0);
}

static void run_case(const char* executable, const char* mode, int tuple) {
    SplArray* args = rt_array_new(1);
    rt_array_push(args, rt_string_new((const uint8_t*)mode, strlen(mode)));
    int64_t out, err, status;
    int64_t timeout = strcmp(mode,"timeout") == 0 ? 1000 : 3000;
    int64_t cap = strcmp(mode,"capped") == 0 ? 2 : 64;
    if (tuple) {
        int64_t* result = rt_process_run_bounded_tuple(executable, strlen(executable), args, timeout, cap);
        CHECK(result != NULL);
        if (!result) return;
        out=result[0]; err=result[1]; status=result[2];
        free(result);
    } else {
        SplArray* result = rt_process_run_bounded(executable, strlen(executable), args, timeout, cap);
        CHECK(result != NULL);
        if (!result) return;
        out=rt_array_get(result,0); err=rt_array_get(result,1);
        status=rt_value_as_int(rt_array_get(result,2));
    }
    if (strcmp(mode,"empty") == 0) {
        check_text(out,(const unsigned char*)"",0); check_text(err,(const unsigned char*)"",0);
        CHECK(status == 0);
    } else if (strcmp(mode,"timeout") == 0) {
        check_text(out,output,sizeof output);
        CHECK(rt_string_len(err) > (int64_t)sizeof error);
        if (rt_string_len(err) > (int64_t)sizeof error) {
            CHECK(memcmp(rt_string_data(err),error,sizeof error) == 0);
            CHECK(strstr((const char*)rt_string_data(err)+sizeof error,"[TIMEOUT:") != NULL);
        }
        CHECK(status == -1);
    } else if (strcmp(mode,"capped") == 0) {
        static const unsigned char capped_out[]="A\n[output truncated: 2 bytes omitted]\n\0";
        static const unsigned char capped_err[]="E\n[output truncated: 2 bytes omitted]\n\0";
        check_text(out,capped_out,sizeof capped_out-1); check_text(err,capped_err,sizeof capped_err-1);
        CHECK(status == 23);
    } else {
        check_text(out,output,sizeof output); check_text(err,error,sizeof error);
        CHECK(status == 23);
    }
}

int main(int argc, char** argv) {
    if (argc == 2) {
        if (!strcmp(argv[1],"empty")) return 0;
        _setmode(_fileno(stdout),_O_BINARY); _setmode(_fileno(stderr),_O_BINARY);
        if (_write(_fileno(stdout),output,sizeof output) != sizeof output) return 90;
        if (_write(_fileno(stderr),error,sizeof error) != sizeof error) return 91;
        if (!strcmp(argv[1],"timeout")) Sleep(10000);
        return 23;
    }
    __simple_runtime_init();
    for (int tuple=0;tuple<2;++tuple) {
        run_case(argv[0],"bytes",tuple); run_case(argv[0],"capped",tuple);
        run_case(argv[0],"timeout",tuple); run_case(argv[0],"empty",tuple);
    }
    if (failures) return 1;
    puts("PASS: Windows text and tuple NUL bytes, status, bound, timeout, reset");
    return 0;
}
