/* Native Windows authority regression. Build with the canonical provider:
 * gcc -std=c11 -Wall -Wextra -Wno-unused-parameter this.c
 *     src/runtime/runtime_cache_host_authority_v1.c -o authority.exe
 * The test creates and removes only its own unique temporary directory. */
#include <windows.h>
#include <winioctl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <wchar.h>

int64_t rt_cache_host_open_root_v1(const uint8_t *,int64_t);
int64_t rt_cache_host_open_read_v1(int64_t,const uint8_t *,int64_t);
int64_t rt_cache_host_size_v1(int64_t,int64_t);
int64_t rt_cache_host_pread_receipt_v1(int64_t,int64_t,uint8_t *,int64_t);
int64_t rt_cache_host_secure_temp_v1(int64_t);
int64_t rt_cache_host_write_temp_v1(int64_t,int64_t,const uint8_t *,int64_t);
int64_t rt_cache_host_publish_noreplace_v1(int64_t,const uint8_t *,int64_t);
int64_t rt_cache_host_fsync_v1(int64_t);
int64_t rt_cache_host_close_v1(int64_t);
int64_t rt_cache_host_namespace_available_v3(void);
int64_t rt_cache_host_mutation_scope_available_v1(void);
static int checks;
#define CHECK(x) do { ++checks; if (!(x)) { fprintf(stderr,"FAIL line %d: %s (winerr %lu)\n",__LINE__,#x,(unsigned long)GetLastError()); exit(1); } } while (0)
static int utf8(const wchar_t *w,char *out,int cap) {
    int n=WideCharToMultiByte(CP_UTF8,WC_ERR_INVALID_CHARS,w,-1,out,cap,NULL,NULL);
    CHECK(n>0); return n-1;
}
static int64_t root_handle(const wchar_t *w) {
    char p[32768]; int n=utf8(w,p,sizeof p);
    return rt_cache_host_open_root_v1((const uint8_t *)p,n);
}
static int64_t read_handle(int64_t root,const char *p) {
    return rt_cache_host_open_read_v1(root,(const uint8_t *)p,(int64_t)strlen(p));
}
static int64_t publish(int64_t temp,const char *p) {
    return rt_cache_host_publish_noreplace_v1(temp,(const uint8_t *)p,(int64_t)strlen(p));
}
static void path_join(wchar_t *out,const wchar_t *root,const wchar_t *name) {
    swprintf(out,32760,L"%ls\\%ls",root,name);
}
static void fixture(const wchar_t *p,const char *bytes) {
    HANDLE h=CreateFileW(p,GENERIC_WRITE,0,NULL,CREATE_NEW,FILE_ATTRIBUTE_NORMAL,NULL);
    CHECK(h!=INVALID_HANDLE_VALUE); DWORD written;
    CHECK(WriteFile(h,bytes,(DWORD)strlen(bytes),&written,NULL) && written==strlen(bytes));
    CHECK(CloseHandle(h));
}
static void remove_fixture(const wchar_t *p) {
    CHECK(SetFileAttributesW(p,FILE_ATTRIBUTE_NORMAL)); CHECK(DeleteFileW(p));
}
/* Junctions require no symlink privilege. This makes the reparse rejection
 * mandatory on normal Windows developer hosts instead of silently skipping. */
static void junction(const wchar_t *path,const wchar_t *target) {
    CHECK(CreateDirectoryW(path,NULL));
    HANDLE h=CreateFileW(path,GENERIC_WRITE,0,NULL,OPEN_EXISTING,
        FILE_FLAG_OPEN_REPARSE_POINT|FILE_FLAG_BACKUP_SEMANTICS,NULL);
    CHECK(h!=INVALID_HANDLE_VALUE);
    struct junction_data {
        DWORD tag; WORD bytes,reserved;
        WORD sub_offset,sub_bytes,print_offset,print_bytes;
        wchar_t names[32760];
    } *data=calloc(1,sizeof *data);
    CHECK(data!=NULL);
    /* Target already uses \\?\ drive syntax; junction substitute uses \??\. */
    swprintf(data->names,32760,L"\\??\\%ls",target+4);
    size_t sub=wcslen(data->names), printable=wcslen(target);
    memcpy(data->names+sub+1,target,(printable+1)*sizeof(wchar_t));
    data->tag=IO_REPARSE_TAG_MOUNT_POINT;
    data->sub_bytes=(WORD)(sub*sizeof(wchar_t));
    data->print_offset=(WORD)((sub+1)*sizeof(wchar_t));
    data->print_bytes=(WORD)(printable*sizeof(wchar_t));
    data->bytes=(WORD)(8+(sub+1+printable+1)*sizeof(wchar_t));
    DWORD returned;
    CHECK(DeviceIoControl(h,FSCTL_SET_REPARSE_POINT,data,data->bytes+8,NULL,0,&returned,NULL));
    free(data); CHECK(CloseHandle(h));
}
int main(void) {
    wchar_t temp[32760], base[32760], root[32760], path[32760], renamed[32760], link[32760];
    CHECK(GetTempPathW(32760,temp)>0);
    swprintf(base,32760,L"\\\\?\\%lssimple-authority-%lu-%llu",temp,
        (unsigned long)GetCurrentProcessId(),(unsigned long long)GetTickCount64());
    CHECK(CreateDirectoryW(base,NULL));
    wcscpy(root,base);
    wchar_t levels[4][32760];
    for (int i=0;i<4;++i) {
        swprintf(path,32760,L"%ls\\unicode-\x03bb-\xd55c-012345678901234567890123456789012345678901234567890123456789-%d",root,i);
        CHECK(CreateDirectoryW(path,NULL)); wcscpy(root,path); wcscpy(levels[i],root);
    }
    CHECK(wcslen(root)>260);
    path_join(path,root,L"object.bin"); fixture(path,"original receipt bytes");
    path_join(path,root,L"empty.bin"); fixture(path,"");
    path_join(path,root,L"nested"); CHECK(CreateDirectoryW(path,NULL));
    path_join(path,root,L"nested\\nested.bin"); fixture(path,"nested");
    path_join(link,root,L"escape"); junction(link,base);
    CHECK(root_handle(link)==-1);
    int64_t r=root_handle(root); CHECK(r>0);
    CHECK(rt_cache_host_fsync_v1(r)==1);
    CHECK(read_handle(r,"escape/object.bin")==-1);
    const char *bad[]={"","/object.bin","../object.bin","nested/../object.bin","./object.bin",
        "nested//nested.bin","nested/","nested\\nested.bin","object.bin:stream","CON","NUL.txt","object.bin.","object.bin ","C:/object.bin"};
    for (unsigned i=0;i<sizeof bad/sizeof bad[0];++i) CHECK(read_handle(r,bad[i])==-1);
    CHECK(rt_cache_host_open_root_v1((const uint8_t *)"relative",8)==-1);
    CHECK(rt_cache_host_open_root_v1((const uint8_t *)"C:/../",6)==-1);
    CHECK(rt_cache_host_open_root_v1((const uint8_t *)"C:/a\0b",6)==-1);
    const uint8_t invalid[]={0xff}; CHECK(rt_cache_host_open_root_v1(invalid,1)==-1);
    CHECK(rt_cache_host_size_v1(0,100)==-1);
    CHECK(rt_cache_host_size_v1(r,100)==-1);
    CHECK(rt_cache_host_secure_temp_v1(-1)==-1);
    int64_t object=read_handle(r,"object.bin"); CHECK(object>0);
    /* Production entry-object publication requires this barrier. It remains
     * unsupported: a read handle must never pretend it has flush authority. */
    CHECK(rt_cache_host_fsync_v1(object)==-1);
    CHECK(rt_cache_host_size_v1(object,100)==22);
    CHECK(rt_cache_host_size_v1(object,21)==-1);
    CHECK(rt_cache_host_size_v1(object,67108865)==-1);
    uint8_t receipt[100], again[100];
    CHECK(rt_cache_host_pread_receipt_v1(object,0,receipt,sizeof receipt)==22);
    CHECK(!memcmp(receipt,"original receipt bytes",22));
    CHECK(rt_cache_host_pread_receipt_v1(object,0,again,21)==-1);
    CHECK(rt_cache_host_pread_receipt_v1(object,1,again,sizeof again)==-1);
    CHECK(rt_cache_host_pread_receipt_v1(object,0,NULL,100)==-1);
    path_join(path,root,L"object.bin");
    HANDLE writer=CreateFileW(path,GENERIC_WRITE,FILE_SHARE_READ|FILE_SHARE_WRITE|FILE_SHARE_DELETE,NULL,OPEN_EXISTING,0,NULL);
    CHECK(writer==INVALID_HANDLE_VALUE && GetLastError()==ERROR_SHARING_VIOLATION);
    path_join(renamed,root,L"replaced.bin"); CHECK(!MoveFileExW(path,renamed,0));
    swprintf(renamed,32760,L"%ls-swapped",root); CHECK(!MoveFileExW(root,renamed,0));
    CHECK(rt_cache_host_pread_receipt_v1(object,0,again,sizeof again)==22 && !memcmp(receipt,again,22));
    int64_t empty=read_handle(r,"empty.bin"); CHECK(empty>0);
    CHECK(rt_cache_host_size_v1(empty,0)==0);
    CHECK(rt_cache_host_pread_receipt_v1(empty,0,again,0)==0);
    CHECK(rt_cache_host_close_v1(empty)==0);
    CHECK(rt_cache_host_size_v1(empty,100)==-1);
    int64_t nested=read_handle(r,"nested/nested.bin"); CHECK(nested>0);
    path_join(path,root,L"nested"); path_join(renamed,root,L"nested-swapped"); CHECK(!MoveFileExW(path,renamed,0));
    CHECK(rt_cache_host_close_v1(nested)==0);
    int64_t t=rt_cache_host_secure_temp_v1(r); CHECK(t>0);
    CHECK(rt_cache_host_write_temp_v1(t,0,(const uint8_t *)"published",9)==9);
    CHECK(rt_cache_host_write_temp_v1(t,67108864,(const uint8_t *)"x",1)==-1);
    CHECK(rt_cache_host_write_temp_v1(object,0,(const uint8_t *)"x",1)==-1);
    CHECK(rt_cache_host_fsync_v1(t)==1);
    CHECK(publish(t,"../bad")==-1);
    CHECK(publish(t,"published.bin")==1);
    CHECK(rt_cache_host_close_v1(t)==-1);
    path_join(path,root,L"published.bin"); CHECK(GetFileAttributesW(path)&FILE_ATTRIBUTE_READONLY);
    t=rt_cache_host_secure_temp_v1(r); CHECK(t>0);
    CHECK(rt_cache_host_write_temp_v1(t,0,(const uint8_t *)"overwrite",9)==9);
    CHECK(publish(t,"published.bin")==0);
    CHECK(rt_cache_host_write_temp_v1(t,0,(const uint8_t *)"x",1)==-1);
    CHECK(rt_cache_host_close_v1(t)==0);
    int64_t published=read_handle(r,"published.bin"); CHECK(published>0);
    CHECK(rt_cache_host_fsync_v1(published)==-1);
    CHECK(rt_cache_host_pread_receipt_v1(published,0,again,100)==9 && !memcmp(again,"published",9));
    CHECK(rt_cache_host_close_v1(published)==0);
    t=rt_cache_host_secure_temp_v1(r); CHECK(t>0);
    CHECK(rt_cache_host_close_v1(r)==0); /* descendants retain ancestry */
    CHECK(publish(t,"empty-published.bin")==1);
    CHECK(rt_cache_host_close_v1(object)==0);
    CHECK(rt_cache_host_close_v1(object)==-1);
    CHECK(rt_cache_host_namespace_available_v3()==-3);
    CHECK(rt_cache_host_mutation_scope_available_v1()==-1);
    path_join(path,root,L"published.bin"); remove_fixture(path);
    path_join(path,root,L"empty-published.bin"); remove_fixture(path);
    path_join(path,root,L"object.bin"); remove_fixture(path);
    path_join(path,root,L"empty.bin"); remove_fixture(path);
    path_join(path,root,L"nested\\nested.bin"); remove_fixture(path);
    path_join(path,root,L"nested"); CHECK(RemoveDirectoryW(path));
    CHECK(RemoveDirectoryW(link));
    for (int i=3;i>=0;--i) CHECK(RemoveDirectoryW(levels[i]));
    CHECK(RemoveDirectoryW(base));
    printf("PASS Windows cache file authority: %d checks\n",checks); return 0;
}
