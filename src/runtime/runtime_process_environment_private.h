#ifndef SIMPLE_WINDOWS_CHILD_ENV_PRIVATE_V1_H
#define SIMPLE_WINDOWS_CHILD_ENV_PRIVATE_V1_H
/* Private, copied UTF-16 environment blocks. No SetEnvironmentVariable calls. */
#ifdef _WIN32
#include <windows.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <wchar.h>
#include <limits.h>

#define WIN_CHILD_ENV_MAX_ENTRIES_V1 65536u
#define WIN_CHILD_ENV_MAX_UNITS_V1 1048576u
struct WinChildEnvPairV1 { const char* key; size_t key_len; const char* value; size_t value_len; };
struct WinChildEnvEntryV1 { wchar_t* key; wchar_t* value; size_t key_len; size_t value_len; };

static wchar_t* win_child_env_utf8_v1(const char* value,size_t length,DWORD* error) {
    if ((!value&&length)||length>4u*WIN_CHILD_ENV_MAX_UNITS_V1||length>INT_MAX||(length&&memchr(value,0,length))) { *error=ERROR_INVALID_PARAMETER;return NULL; }
    if (!length) { wchar_t* out=(wchar_t*)calloc(1,sizeof(wchar_t));if(!out)*error=ERROR_NOT_ENOUGH_MEMORY;return out; }
    int size=MultiByteToWideChar(CP_UTF8,MB_ERR_INVALID_CHARS,value,(int)length,NULL,0);
    if(size<=0) { *error=GetLastError();return NULL; }
    wchar_t* out=(wchar_t*)calloc((size_t)size+1,sizeof(wchar_t));
    if(!out) { *error=ERROR_NOT_ENOUGH_MEMORY;return NULL; }
    if(MultiByteToWideChar(CP_UTF8,MB_ERR_INVALID_CHARS,value,(int)length,out,size)!=size) { *error=GetLastError();free(out);return NULL; }
    return out;
}
static int win_child_env_name_valid_v1(const wchar_t* key,size_t length) {
    if(!key||!length||length>32767)return 0;
    if(key[0]==L'=')return length==3&&((key[1]>=L'A'&&key[1]<=L'Z')||(key[1]>=L'a'&&key[1]<=L'z'))&&key[2]==L':';
    for(size_t i=0;i<length;i++)if(key[i]==L'=')return 0;
    return 1;
}
static wchar_t* win_child_env_wcopy_v1(const wchar_t* value,size_t length) {
    if(length>WIN_CHILD_ENV_MAX_UNITS_V1)return NULL;
    wchar_t* out=(wchar_t*)calloc(length+1,sizeof(wchar_t));
    if(out)memcpy(out,value,length*sizeof(wchar_t));return out;
}
static int win_child_env_equal_v1(const struct WinChildEnvEntryV1* a,const struct WinChildEnvEntryV1* b) {
    return CompareStringOrdinal(a->key,(int)a->key_len,b->key,(int)b->key_len,TRUE)==CSTR_EQUAL;
}
static int win_child_env_order_v1(const void* av,const void* bv) {
    const struct WinChildEnvEntryV1* a=(const struct WinChildEnvEntryV1*)av;
    const struct WinChildEnvEntryV1* b=(const struct WinChildEnvEntryV1*)bv;
    int result=CompareStringOrdinal(a->key,(int)a->key_len,b->key,(int)b->key_len,TRUE);
    return result==CSTR_LESS_THAN?-1:result==CSTR_GREATER_THAN?1:0;
}
static void win_child_env_free_entries_v1(struct WinChildEnvEntryV1* entries,size_t used) {
    if(entries){for(size_t i=0;i<used;i++){free(entries[i].key);free(entries[i].value);}free(entries);}
}
/* inherit=0: exact replacement, including the empty block. inherit=1: snapshot
 * parent privately then overlay case-insensitively. An empty value is present,
 * not deletion. Duplicate requested aliases reject; valid hidden =C: keys stay. */
static wchar_t* win_child_environment_v1(const struct WinChildEnvPairV1* pairs,size_t count,int inherit,DWORD* error) {
    DWORD local_error=0;if(!error)error=&local_error;*error=0;
    if((inherit!=0&&inherit!=1)||count>WIN_CHILD_ENV_MAX_ENTRIES_V1||(count&&!pairs)){*error=ERROR_INVALID_PARAMETER;return NULL;}
    struct WinChildEnvEntryV1* requested=(struct WinChildEnvEntryV1*)calloc(count?count:1,sizeof(*requested));
    struct WinChildEnvEntryV1* entries=NULL;size_t used=0,capacity=0,requested_used=0;wchar_t* block=NULL;LPWCH snapshot=NULL;
    if(!requested){*error=ERROR_NOT_ENOUGH_MEMORY;return NULL;}
    size_t input_bytes=0;
    for(size_t i=0;i<count;i++) {
        if(pairs[i].key_len>4u*WIN_CHILD_ENV_MAX_UNITS_V1-input_bytes){*error=ERROR_BUFFER_OVERFLOW;goto done;}
        input_bytes+=pairs[i].key_len;
        if(pairs[i].value_len>4u*WIN_CHILD_ENV_MAX_UNITS_V1-input_bytes){*error=ERROR_BUFFER_OVERFLOW;goto done;}
        input_bytes+=pairs[i].value_len;
        requested[i].key=win_child_env_utf8_v1(pairs[i].key,pairs[i].key_len,error);
        requested[i].value=win_child_env_utf8_v1(pairs[i].value,pairs[i].value_len,error);requested_used=i+1;
        if(!requested[i].key||!requested[i].value)goto done;
        requested[i].key_len=wcslen(requested[i].key);requested[i].value_len=wcslen(requested[i].value);
        if(!win_child_env_name_valid_v1(requested[i].key,requested[i].key_len)){*error=ERROR_INVALID_PARAMETER;goto done;}
    }
    qsort(requested,count,sizeof(*requested),win_child_env_order_v1);
    for(size_t i=1;i<count;i++)if(win_child_env_equal_v1(&requested[i-1],&requested[i])){*error=ERROR_INVALID_PARAMETER;goto done;}
    if(inherit) {
        snapshot=GetEnvironmentStringsW();if(!snapshot){*error=GetLastError();goto done;}
        size_t snapshot_units=1;
        for(const wchar_t* item=snapshot;*item;item+=wcslen(item)+1) {
            if(used>=WIN_CHILD_ENV_MAX_ENTRIES_V1){*error=ERROR_BUFFER_OVERFLOW;goto done;}
            const wchar_t* separator=wcschr(item+(item[0]==L'='?1:0),L'=');
            if(!separator){*error=ERROR_BAD_ENVIRONMENT;goto done;}
            size_t key_len=(size_t)(separator-item),value_len=wcslen(separator+1);
            size_t entry_units=key_len+value_len+2;
            if(entry_units>WIN_CHILD_ENV_MAX_UNITS_V1-snapshot_units){*error=ERROR_BUFFER_OVERFLOW;goto done;}snapshot_units+=entry_units;
            if(!win_child_env_name_valid_v1(item,key_len)){*error=ERROR_BAD_ENVIRONMENT;goto done;}
            if(used==capacity) {
                size_t next=capacity?capacity*2:64;if(next>WIN_CHILD_ENV_MAX_ENTRIES_V1)next=WIN_CHILD_ENV_MAX_ENTRIES_V1;
                struct WinChildEnvEntryV1* grown=(struct WinChildEnvEntryV1*)realloc(entries,next*sizeof(*entries));
                if(!grown){*error=ERROR_NOT_ENOUGH_MEMORY;goto done;}entries=grown;capacity=next;
            }
            struct WinChildEnvEntryV1 entry={win_child_env_wcopy_v1(item,key_len),win_child_env_wcopy_v1(separator+1,value_len),key_len,value_len};
            if(!entry.key||!entry.value){free(entry.key);free(entry.value);*error=ERROR_NOT_ENOUGH_MEMORY;goto done;}
            entries[used++]=entry;
        }
        qsort(entries,used,sizeof(*entries),win_child_env_order_v1);
        for(size_t i=1;i<used;i++)if(win_child_env_equal_v1(&entries[i-1],&entries[i])){*error=ERROR_BAD_ENVIRONMENT;goto done;}
    }
    /* Merge two sorted unique lists in O(n+m), replacing parent aliases. */
    size_t merged_count=used+count;
    struct WinChildEnvEntryV1* merged=(struct WinChildEnvEntryV1*)calloc(merged_count?merged_count:1,sizeof(*merged));
    if(!merged){*error=ERROR_NOT_ENOUGH_MEMORY;goto done;}
    size_t a=0,b=0,m=0;
    while(a<used||b<count) {
        int order=a==used?1:b==count?-1:win_child_env_order_v1(&entries[a],&requested[b]);
        if(order<0){merged[m++]=entries[a];entries[a].key=NULL;entries[a].value=NULL;a++;}
        else {
            if(order==0){free(entries[a].key);free(entries[a].value);entries[a].key=NULL;entries[a].value=NULL;a++;}
            merged[m++]=requested[b];requested[b].key=NULL;requested[b].value=NULL;b++;
        }
    }
    win_child_env_free_entries_v1(entries,used);entries=merged;used=m;capacity=merged_count;
    if(used>WIN_CHILD_ENV_MAX_ENTRIES_V1){*error=ERROR_BUFFER_OVERFLOW;goto done;}
    size_t units=used?1:2;
    for(size_t i=0;i<used;i++) {
        size_t entry_units=entries[i].key_len+1+entries[i].value_len+1;
        if(entry_units>WIN_CHILD_ENV_MAX_UNITS_V1-units){*error=ERROR_BUFFER_OVERFLOW;goto done;}units+=entry_units;
    }
    block=(wchar_t*)calloc(units,sizeof(wchar_t));if(!block){*error=ERROR_NOT_ENOUGH_MEMORY;goto done;}
    wchar_t* out=block;
    for(size_t i=0;i<used;i++) {
        memcpy(out,entries[i].key,entries[i].key_len*sizeof(wchar_t));out+=entries[i].key_len;*out++=L'=';
        memcpy(out,entries[i].value,entries[i].value_len*sizeof(wchar_t));out+=entries[i].value_len;*out++=0;
    }
    /* calloc supplies final NUL, and two NULs for an exact empty block. */
 done:
    if(snapshot)FreeEnvironmentStringsW(snapshot);
    win_child_env_free_entries_v1(entries,used);win_child_env_free_entries_v1(requested,requested_used);
    return block;
}
#endif
#endif
