/* Windows rt_env_vars owner regression.
 * Link with the actual core-C runtime composition. Run without arguments for
 * real Win32/UTF-8/empty/missing/snapshot/hidden-drive behavior. For --failures,
 * compile only runtime_native.c with rt_windows_env_snapshot_faults.h forced
 * into that translation unit; all successful acquisitions still use Win32.
 * The failure mode verifies nil results and OS-block/heap cleanup. No ambient
 * environment values are printed, and all mutated names are process-local.
 */
#ifdef NDEBUG
#error Assertions must remain enabled
#endif
#ifndef _WIN32
#error This check requires the actual Windows environment block
#endif
#include <windows.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <wchar.h>
extern bool rt_env_set(const uint8_t*,uint64_t,const uint8_t*,uint64_t);
extern int8_t rt_env_remove(const uint8_t*,uint64_t);
extern int64_t rt_env_vars(void);
extern int64_t rt_array_len(void*);
extern int64_t rt_array_get(void*,int64_t);
extern void rt_array_free(void*);
extern int64_t rt_tuple_get(int64_t,int64_t);
extern int64_t rt_string_len(int64_t);
extern const uint8_t* rt_string_data(int64_t);
extern int64_t rt_string_free(int64_t);
extern int64_t rt_heap_registry_count(void);
static int fail_snapshot;
static unsigned blocks_acquired,blocks_freed;
LPWCH WINAPI p0_thread_runtime_get_environment_strings(void) {
    if (fail_snapshot) { SetLastError(ERROR_NOT_ENOUGH_MEMORY); return NULL; }
    LPWCH result=GetEnvironmentStringsW();
    if (result) blocks_acquired++;
    return result;
}
BOOL WINAPI p0_thread_runtime_free_environment_strings(LPWCH block) {
    BOOL result=FreeEnvironmentStringsW(block);
    if (result) blocks_freed++;
    return result;
}
static unsigned checks,failures;
static char names[5][128];
static void p0_thread_runtime_check(int ok,const char* label) {
    checks++;
    if(!ok) { failures++; fprintf(stderr,"FAIL: %s\n",label); }
}
static int text_equals(int64_t text,const char* expected) {
    size_t length=strlen(expected);
    const uint8_t* bytes=rt_string_data(text);
    return rt_string_len(text)==(int64_t)length && (!length || (bytes && !memcmp(bytes,expected,length)));
}
static int pair_count(int64_t snapshot,const char* key,const char* value) {
    if(snapshot==3 || snapshot==0) return -1;
    int count=0;
    for(int64_t i=0;i<rt_array_len((void*)(uintptr_t)snapshot);i++) {
        int64_t pair=rt_array_get((void*)(uintptr_t)snapshot,i);
        if(text_equals(rt_tuple_get(pair,0),key) && (!value || text_equals(rt_tuple_get(pair,1),value))) count++;
    }
    return count;
}
static void snapshot_free(int64_t snapshot) {
    if(snapshot==3 || snapshot==0) return;
    for(int64_t i=0;i<rt_array_len((void*)(uintptr_t)snapshot);i++) {
        int64_t pair=rt_array_get((void*)(uintptr_t)snapshot,i);
        rt_string_free(rt_tuple_get(pair,0)); rt_string_free(rt_tuple_get(pair,1));
        rt_array_free((void*)(uintptr_t)pair);
    }
    rt_array_free((void*)(uintptr_t)snapshot);
}
static void p0_thread_runtime_cleanup(void) {
    for(int i=0;i<5;i++) if(names[i][0]) rt_env_remove((const uint8_t*)names[i],strlen(names[i]));
}
static int hidden_child(void) {
    LPWCH block=GetEnvironmentStringsW(); int found=0;
    for(const wchar_t* e=block;e && *e;e+=wcslen(e)+1) if(!wcscmp(e,L"=Z:=C:\\")) found=1;
    p0_thread_runtime_check(found,"actual child block contains hidden drive entry");
    if(block) FreeEnvironmentStringsW(block);
    int64_t snap=rt_env_vars();
    p0_thread_runtime_check(pair_count(snap,"SIMPLE_ENV_SNAPSHOT_HIDDEN_CONTROL","control")==1,"hidden child public control survives");
    p0_thread_runtime_check(pair_count(snap,"",NULL)==0 && pair_count(snap,"=Z:",NULL)==0,"hidden drive entries excluded from public snapshot");
    snapshot_free(snap);
    return failures?1:0;
}
static void run_hidden_child(void) {
    wchar_t exe[MAX_PATH],command[MAX_PATH*2],system_root[MAX_PATH];
    DWORD n=GetModuleFileNameW(NULL,exe,MAX_PATH);
    DWORD r=GetEnvironmentVariableW(L"SystemRoot",system_root,MAX_PATH);
    if(!n || n>=MAX_PATH || !r || r>=MAX_PATH) { p0_thread_runtime_check(0,"hidden child prerequisites"); return; }
    swprintf(command,MAX_PATH*2,L"\"%ls\" --hidden",exe);
    const wchar_t prefix[]=L"=Z:=C:\\\0SIMPLE_ENV_SNAPSHOT_HIDDEN_CONTROL=control\0SystemRoot=";
    size_t prefix_len=sizeof(prefix)/sizeof(wchar_t)-1;
    wchar_t* environment=calloc(prefix_len+wcslen(system_root)+2,sizeof(wchar_t));
    if(!environment) { p0_thread_runtime_check(0,"hidden child allocation"); return; }
    memcpy(environment,prefix,prefix_len*sizeof(wchar_t));
    memcpy(environment+prefix_len,system_root,wcslen(system_root)*sizeof(wchar_t));
    STARTUPINFOW startup={0}; PROCESS_INFORMATION process={0}; startup.cb=sizeof(startup);
    BOOL started=CreateProcessW(exe,command,NULL,NULL,FALSE,CREATE_UNICODE_ENVIRONMENT|CREATE_NO_WINDOW,environment,NULL,&startup,&process);
    free(environment);
    p0_thread_runtime_check(started!=0,"hidden child created");
    if(!started) return;
    DWORD wait=WaitForSingleObject(process.hProcess,10000),exit_code=1;
    if(wait==WAIT_TIMEOUT) { TerminateProcess(process.hProcess,124); WaitForSingleObject(process.hProcess,1000); }
    GetExitCodeProcess(process.hProcess,&exit_code);
    CloseHandle(process.hThread); CloseHandle(process.hProcess);
    p0_thread_runtime_check(wait==WAIT_OBJECT_0 && exit_code==0,"hidden child actual snapshot contract");
}
static int failure_paths(void) {
    int64_t warm=rt_env_vars(); snapshot_free(warm);
    int64_t heap_before=rt_heap_registry_count();
    unsigned acquired_before=blocks_acquired,freed_before=blocks_freed;
    fail_snapshot=1;
    int64_t missing=rt_env_vars();
    fail_snapshot=0;
    p0_thread_runtime_check(missing==3,"OS snapshot failure returns nil");
    snapshot_free(missing);
    p0_thread_runtime_check(blocks_acquired==acquired_before && blocks_freed==freed_before,"failed OS acquisition is never freed");
    p0_thread_runtime_check(rt_heap_registry_count()==heap_before,"failed OS acquisition frees result container");
    wchar_t bad_key[128]; swprintf(bad_key,128,L"SIMPLE_ENV_BAD_UTF16_%lu",GetCurrentProcessId());
    const wchar_t invalid_utf16[]={0xd800,0};
    p0_thread_runtime_check(SetEnvironmentVariableW(bad_key,invalid_utf16)!=0,"install real malformed UTF16 value");
    heap_before=rt_heap_registry_count(); acquired_before=blocks_acquired; freed_before=blocks_freed;
    int64_t bad=rt_env_vars();
    p0_thread_runtime_check(bad==3,"invalid UTF16 does not become partial success");
    snapshot_free(bad);
    p0_thread_runtime_check(blocks_acquired==acquired_before+1 && blocks_freed==freed_before+1,"conversion failure frees exact acquired OS block");
    p0_thread_runtime_check(rt_heap_registry_count()==heap_before,"conversion failure frees partial tuples and strings");
    p0_thread_runtime_check(SetEnvironmentVariableW(bad_key,NULL)!=0,"remove malformed value");
    printf("windows_env_snapshot_failures: %s (%u checks, %u failures)\n",failures?"FAIL":"PASS",checks,failures);
    return failures?1:0;
}
int main(int argc,char**argv) {
    if(argc==2 && !strcmp(argv[1],"--hidden")) return hidden_child();
    if(argc==2 && !strcmp(argv[1],"--failures")) return failure_paths();
    for(int i=0;i<5;i++) snprintf(names[i],sizeof(names[i]),"SIMPLE_ENV_SNAPSHOT_%lu_%d",GetCurrentProcessId(),i);
    atexit(p0_thread_runtime_cleanup);
    const char* unicode_key_suffix="_\xe9\x9b\xaa";
    strcat(names[1],unicode_key_suffix);
    const char* values[]={"left=middle=right","caf\xc3\xa9 \xf0\x9f\x90\x89",""};
    for(int i=0;i<3;i++) p0_thread_runtime_check(rt_env_set((const uint8_t*)names[i],strlen(names[i]),(const uint8_t*)values[i],strlen(values[i])),"set UTF8 boundary variable");
    p0_thread_runtime_check(rt_env_remove((const uint8_t*)names[3],strlen(names[3])),"remove missing sentinel");
    wchar_t raw_key[128]; MultiByteToWideChar(CP_UTF8,MB_ERR_INVALID_CHARS,names[4],-1,raw_key,128);
    p0_thread_runtime_check(SetEnvironmentVariableW(raw_key,L"win32-only")!=0,"Win32-only setter");
    int64_t first=rt_env_vars();
    p0_thread_runtime_check(pair_count(first,names[0],values[0])==1,"ASCII and embedded equals");
    p0_thread_runtime_check(pair_count(first,names[1],values[1])==1,"UTF8 key and non-BMP value");
    p0_thread_runtime_check(pair_count(first,names[2],"")==1,"explicit empty value preserved exactly once");
    p0_thread_runtime_check(pair_count(first,names[3],NULL)==0,"missing remains absent");
    p0_thread_runtime_check(pair_count(first,names[4],"win32-only")==1,"direct Win32 writes visible");
    p0_thread_runtime_check(SetEnvironmentVariableW(raw_key,L"changed")!=0,"update Win32-only setter");
    int64_t second=rt_env_vars();
    p0_thread_runtime_check(pair_count(first,names[4],"win32-only")==1,"first snapshot immutable after update");
    p0_thread_runtime_check(pair_count(second,names[4],"changed")==1,"new snapshot reflects update");
    snapshot_free(first); snapshot_free(second);
    p0_thread_runtime_cleanup();
    int64_t removed=rt_env_vars();
    for(int i=0;i<5;i++) p0_thread_runtime_check(pair_count(removed,names[i],NULL)==0,"removed variable absent");
    snapshot_free(removed);
    run_hidden_child();
    printf("windows_env_snapshot: %s (%u checks, %u failures)\n",failures?"FAIL":"PASS",checks,failures);
    return failures?1:0;
}
