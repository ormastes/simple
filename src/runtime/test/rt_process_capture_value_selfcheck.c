/* Production tagged-value and native tuple integration for binary captures.
 * Link real runtime_native.c and runtime_process.c, never the test value adapter.
 * argv[1] names the compiled rt_process_capture_bytes_selfcheck child fixture.
 */
#include "runtime.h"
#include <stdio.h>
#include <string.h>
#include <stdint.h>

extern int64_t* rt_process_run_bounded_tuple(int64_t, SplArray*, int64_t, int64_t);
static int failures, cases;
static int text_is(int64_t value, const void* bytes, size_t length) {
    const uint8_t* data = rt_string_data(value);
    return rt_string_len(value) == (int64_t)length && data
        && !memcmp(data, bytes, length) && data[length] == 0;
}
static void check(const char* name, int ok) {
    cases++; failures += !ok;
    printf("ABI %s %s\n", name, ok ? "PASS" : "FAIL");
}
static SplArray* args_for(const char* mode) {
    SplArray* args = rt_array_new(2);
    rt_array_push(args, rt_string_new((const uint8_t*)"--child", 7));
    rt_array_push(args, rt_string_new((const uint8_t*)mode, strlen(mode)));
    return args;
}
int main(int argc, char** argv) {
    if (argc != 2) { fputs("ERROR: child fixture path required\n",stderr); return 2; }
    const char* child = argv[1];
    SplArray* args = args_for("binary");
    SplArray* result = rt_process_run_bounded(child,strlen(child),args,3000,8);
    check("tagged-array-nul", rt_array_len(result)==3
        && text_is(rt_array_get(result,0),"\0a\0bc\0d\0",8)
        && text_is(rt_array_get(result,1),"e\0r\0",4)
        && rt_value_as_int(rt_array_get(result,2))==0);
    int64_t command = rt_string_new((const uint8_t*)child,strlen(child));
    int64_t* tuple = rt_process_run_bounded_tuple(command,args,3000,8);
    check("native-tuple-nul", tuple && text_is(tuple[0],"\0a\0bc\0d\0",8)
        && text_is(tuple[1],"e\0r\0",4) && tuple[2]==0);
    args = args_for("records");
    tuple = rt_process_run_bounded_tuple(command,args,3000,128);
    const char records[] = "R  new name.spl\0old name.spl\0?? next.spl\0";
    check("native-tuple-git-records", tuple && text_is(tuple[0],records,sizeof(records)-1)
        && text_is(tuple[1],"",0) && tuple[2]==0);
    args = args_for("empty");
    tuple = rt_process_run_bounded_tuple(command,args,3000,16);
    check("native-tuple-empty-after-nul", tuple && text_is(tuple[0],"",0)
        && text_is(tuple[1],"",0) && tuple[2]==0);
    args = args_for("text");
    tuple = rt_process_run_bounded_tuple(command,args,3000,16);
    check("native-tuple-text-exit", tuple && text_is(tuple[0],"hello\n",6)
        && text_is(tuple[1],"warning\n",8) && tuple[2]==7);
    printf("ABI_RESULT cases=%d failures=%d\n",cases,failures);
    return failures ? 1 : 0;
}
