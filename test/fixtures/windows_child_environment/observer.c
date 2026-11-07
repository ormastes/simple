#define _WIN32_WINNT 0x0600
#include <windows.h>
#include <tlhelp32.h>
#include <stdio.h>
#include <stdlib.h>
#include <wchar.h>
#include <string.h>

static int write_failed;
static int write_utf8(HANDLE out,const wchar_t* text) {
    int bytes=WideCharToMultiByte(CP_UTF8,WC_ERR_INVALID_CHARS,text,-1,NULL,0,NULL,NULL);
    if(bytes<=0){write_failed=1;return 0;}char* buffer=(char*)malloc((size_t)bytes);if(!buffer){write_failed=1;return 0;}
    int converted=WideCharToMultiByte(CP_UTF8,WC_ERR_INVALID_CHARS,text,-1,buffer,bytes,NULL,NULL);
    DWORD written=0;int ok=converted==bytes&&WriteFile(out,buffer,(DWORD)(bytes-1),&written,NULL)&&written==(DWORD)(bytes-1);free(buffer);if(!ok)write_failed=1;return ok;
}
static int read_env(const wchar_t* key,wchar_t* value,DWORD capacity,int* present) {
    SetLastError(ERROR_SUCCESS);DWORD length=GetEnvironmentVariableW(key,value,capacity);
    DWORD error=GetLastError();*present=length>0||error==ERROR_SUCCESS;
    if(length>=capacity){value[0]=0;*present=0;return 0;}if(!length)value[0]=0;
    return length>0||error==ERROR_SUCCESS||error==ERROR_ENVVAR_NOT_FOUND;
}
static const wchar_t* separator(const wchar_t* entry) { return wcschr(entry+(entry[0]==L'='?1:0),L'='); }
static int name_is(const wchar_t* item,size_t length,const wchar_t* expected) { return CompareStringOrdinal(item,(int)length,expected,(int)wcslen(expected),TRUE)==CSTR_EQUAL; }
int wmain(int argc,wchar_t** argv) {
    if(argc>=2&&!wcscmp(argv[1],L"--parent-handles")) {
        HANDLE snapshot=CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS,0);if(snapshot==INVALID_HANDLE_VALUE)return 96;
        PROCESSENTRY32W entry={0};entry.dwSize=sizeof(entry);DWORD parent=0,self=GetCurrentProcessId();
        for(BOOL valid=Process32FirstW(snapshot,&entry);valid;valid=Process32NextW(snapshot,&entry))if(entry.th32ProcessID==self){parent=entry.th32ParentProcessID;break;}
        CloseHandle(snapshot);if(!parent)return 96;
        HANDLE process=OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION,FALSE,parent);if(!process)return 96;
        DWORD count=0;BOOL valid=GetProcessHandleCount(process,&count);CloseHandle(process);if(!valid)return 96;
        wchar_t report[80];_snwprintf(report,80,L"parent_handles: %lu\n",(unsigned long)count);
        return write_utf8(GetStdHandle(STD_OUTPUT_HANDLE),report)?0:96;
    }
    if(argc>=2&&!wcscmp(argv[1],L"--empty")) {
        LPWCH block=GetEnvironmentStringsW();if(!block)return 94;
        int empty=block[0]==0&&block[1]==0;FreeEnvironmentStringsW(block);
        write_utf8(GetStdHandle(STD_OUTPUT_HANDLE),empty?L"empty_block: true\n":L"empty_block: false\n");return empty&&!write_failed?0:95;
    }
    if(argc>=2&&!wcscmp(argv[1],L"--sleep")){Sleep(10000);return 0;}
    if(argc>=2&&!wcscmp(argv[1],L"--flood")){char data[4096];memset(data,'x',sizeof(data));for(int i=0;i<64;i++){DWORD n=0;WriteFile(GetStdHandle(STD_OUTPUT_HANDLE),data,sizeof(data),&n,NULL);}return 0;}
    if(argc>=3&&!wcscmp(argv[1],L"--spawn-grandchild")) {
        wchar_t exe[32768],line[32768];DWORD length=GetModuleFileNameW(NULL,exe,32768);if(!length||length>=32760)return 80;
        _snwprintf(line,32768,L"\"%ls\" --sleep",exe);STARTUPINFOW start={0};PROCESS_INFORMATION child={0};start.cb=sizeof(start);
        if(!CreateProcessW(exe,line,NULL,NULL,FALSE,CREATE_NO_WINDOW,NULL,NULL,&start,&child))return 81;
        CloseHandle(child.hThread);CloseHandle(child.hProcess);
        HANDLE marker=CreateFileW(argv[2],GENERIC_WRITE,0,NULL,CREATE_NEW,FILE_ATTRIBUTE_NORMAL,NULL);
        if(marker==INVALID_HANDLE_VALUE)return 82;DWORD n=0;WriteFile(marker,"ready",5,&n,NULL);CloseHandle(marker);Sleep(10000);return 0;
    }
    if(argc<4)return 90;
    int hold=!wcscmp(argv[1],L"--hold");int exact=!wcscmp(argv[3],L"exact");
    if(hold) {
        if(argc<6)return 97;ULONGLONG deadline=GetTickCount64()+5000;
        while(GetFileAttributesW(argv[5])==INVALID_FILE_ATTRIBUTES){if(GetTickCount64()>=deadline)return 98;Sleep(5);}
    }
    HANDLE out=GetStdHandle(STD_OUTPUT_HANDLE);int owned=0;
    if(argc>=5){out=CreateFileW(argv[4],GENERIC_WRITE,0,NULL,CREATE_NEW,FILE_ATTRIBUTE_NORMAL,NULL);if(out==INVALID_HANDLE_VALUE)return 91;owned=1;}
    wchar_t value[32768]={0};int present=0,ok=1;
    if(!read_env(L"SERIAL_CASE",value,32768,&present)||!present||wcscmp(value,argv[2]))ok=0;
    write_utf8(out,L"case: \"");write_utf8(out,value);write_utf8(out,L"\"\n");
    if(!read_env(L"\u0394\u53d8\u91cf",value,32768,&present)||!present||wcscmp(value,L"Gr\u00fc\u00dfe \ud55c\uae00 \U0001f600"))ok=0;
    write_utf8(out,L"unicode: \"");write_utf8(out,value);write_utf8(out,L"\"\n");
    if(!read_env(L"EMPTY",value,32768,&present)||!present||value[0])ok=0;
    write_utf8(out,present&&!value[0]?L"empty_present: true\n":L"empty_present: false\n");
    if(!read_env(L"PARENT_ONLY",value,32768,&present)||present==exact)ok=0;
    write_utf8(out,present?L"parent_only_present: true\n":L"parent_only_present: false\n");
    LPWCH block=GetEnvironmentStringsW();if(!block)return 92;
    const wchar_t* previous=NULL;size_t previous_length=0;int hidden=0,unexpected=0,sorted=1;
    for(const wchar_t* item=block;*item;item+=wcslen(item)+1) {
        const wchar_t* eq=separator(item);if(!eq){ok=0;break;}size_t key_length=(size_t)(eq-item);
        if(previous&&CompareStringOrdinal(previous,(int)previous_length,item,(int)key_length,TRUE)==CSTR_GREATER_THAN)sorted=0;
        previous=item;previous_length=key_length;
        if(name_is(item,key_length,L"=C:")&&!wcscmp(eq+1,L"C:\\"))hidden=1;
        if(exact&&!name_is(item,key_length,L"SERIAL_CASE")&&!name_is(item,key_length,L"EMPTY")&&!name_is(item,key_length,L"\u0394\u53d8\u91cf")&&!name_is(item,key_length,L"=C:"))unexpected++;
    }
    FreeEnvironmentStringsW(block);
    if(!sorted||(exact&&(!hidden||unexpected)))ok=0;
    write_utf8(out,sorted?L"sorted: true\n":L"sorted: false\n");
    write_utf8(out,hidden?L"hidden_drive: true\n":L"hidden_drive: false\n");
    write_utf8(out,unexpected?L"unexpected: true\n":L"unexpected: false\n");
    if(owned)CloseHandle(out);return ok&&!write_failed?0:93;
}
