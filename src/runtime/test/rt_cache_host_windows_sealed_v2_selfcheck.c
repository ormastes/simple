/* Focused manual native probe. Before running, create the dedicated parent
 * C:/dev/p3-retained-seal-probe; each run owns a unique root-PID child.
 * This harness is not claimed to be a generic portable test runner. */
#include "../runtime_cache_host_authority_v1.c"
#include <stdio.h>
static int checks;
#define CHECK(x) do{++checks;if(!(x)){printf("FAIL line%d %s winerr%lu\n",__LINE__,#x,GetLastError());return 1;}}while(0)
static int same(HANDLE h,BY_HANDLE_FILE_INFORMATION *a){BY_HANDLE_FILE_INFORMATION b;return GetFileInformationByHandle(h,&b)&&a->dwVolumeSerialNumber==b.dwVolumeSerialNumber&&a->nFileIndexHigh==b.nFileIndexHigh&&a->nFileIndexLow==b.nFileIndexLow;}
int main(void){
 wchar_t path[256];swprintf(path,256,L"C:\\dev\\p3-retained-seal-probe\\root-%lu",GetCurrentProcessId());CHECK(CreateDirectoryW(path,NULL));char utf[1024];int n=WideCharToMultiByte(CP_UTF8,WC_ERR_INVALID_CHARS,path,-1,utf,sizeof utf,NULL,NULL);CHECK(n>0);
 HANDLE tok;TOKEN_ELEVATION e;DWORD z;CHECK(OpenProcessToken(GetCurrentProcess(),TOKEN_QUERY,&tok));CHECK(GetTokenInformation(tok,TokenElevation,&e,sizeof e,&z));CloseHandle(tok);CHECK(!e.TokenIsElevated);
 int64_t r=rt_cache_host_open_root_v1((uint8_t*)utf,n-1);CHECK(r>0);CHECK(rt_cache_host_fsync_v1(r)==1);
 CHECK(rt_cache_host_publish_retained_noreplace_v2(r,(uint8_t*)"bad",3)<0);CHECK(rt_cache_host_publish_retained_noreplace_v2(-1,(uint8_t*)"bad",3)<0);
 int64_t t=rt_cache_host_secure_temp_v1(r);CHECK(t>0);CHECK(rt_cache_host_write_temp_v1(t,0,(uint8_t*)"original",8)==8);BY_HANDLE_FILE_INFORMATION id;CHECK(GetFileInformationByHandle(cw_file(cw_find(t)),&id));HANDLE original=cw_file(cw_find(t));
 CHECK(rt_cache_host_publish_retained_noreplace_v2(t,(uint8_t*)"../bad",6)<0);CHECK(rt_cache_host_write_temp_v1(t,8,(uint8_t*)"",0)==0);
 int64_t s=rt_cache_host_publish_retained_noreplace_v2(t,(uint8_t*)"caf\xc3\xa9.o",7);CHECK(s>0&&s!=t);CHECK(cw_file(cw_find(s))==original);CHECK(same(original,&id));CHECK(rt_cache_host_write_temp_v1(t,0,(uint8_t*)"x",1)<0);CHECK(rt_cache_host_close_v1(t)<0);CHECK(rt_cache_host_write_temp_v1(s,0,(uint8_t*)"x",1)<0);CHECK(rt_cache_host_publish_noreplace_v1(s,(uint8_t*)"again",5)<0);
 CHECK(rt_cache_host_size_v1(s,8)==8);CHECK(rt_cache_host_size_v1(s,7)<0);uint8_t out[128];CHECK(rt_cache_host_pread_receipt_v1(s,0,out,sizeof out)==8&&!memcmp(out,"original",8));CHECK(rt_cache_host_pread_receipt_v1(s,1,out,sizeof out)<0);CHECK(rt_cache_host_fsync_v1(s)==1);CHECK(rt_cache_host_fsync_v1(r)==1);
 FILE_BASIC_INFO basic;CHECK(GetFileInformationByHandleEx(original,FileBasicInfo,&basic,sizeof basic));CHECK(basic.FileAttributes&FILE_ATTRIBUTE_READONLY);
 int64_t rec=rt_cache_host_secure_temp_v1(r);CHECK(rec>0);const char *receipt="native-capsule-result-v1\nidentity\ncanonical\n8\ndigest\n";int len=(int)strlen(receipt);CHECK(rt_cache_host_write_temp_v1(rec,0,(uint8_t*)receipt,len)==len);int64_t rs=rt_cache_host_publish_retained_noreplace_v2(rec,(uint8_t*)"receipt",7);CHECK(rs>0);CHECK(rt_cache_host_pread_receipt_v1(rs,0,out,sizeof out)==len&&!memcmp(out,receipt,len));CHECK(rt_cache_host_fsync_v1(rs)==1);CHECK(rt_cache_host_fsync_v1(s)==1);CHECK(rt_cache_host_fsync_v1(r)==1);
 int64_t collision=rt_cache_host_secure_temp_v1(r);CHECK(collision>0);CHECK(rt_cache_host_write_temp_v1(collision,0,(uint8_t*)"replacement",11)==11);CHECK(rt_cache_host_publish_retained_noreplace_v2(collision,(uint8_t*)"caf\xc3\xa9.o",7)==0);CHECK(rt_cache_host_close_v1(collision)==0);CHECK(rt_cache_host_pread_receipt_v1(s,0,out,sizeof out)==8&&!memcmp(out,"original",8));CHECK(rt_cache_host_pread_receipt_v1(rs,0,out,sizeof out)==len&&!memcmp(out,receipt,len));
 CHECK(rt_cache_host_close_v1(s)==0);CHECK(rt_cache_host_fsync_v1(s)<0);CHECK(rt_cache_host_pread_receipt_v1(s,0,out,sizeof out)<0);CHECK(rt_cache_host_close_v1(s)<0);
 int64_t rd=rt_cache_host_open_read_v1(r,(uint8_t*)"caf\xc3\xa9.o",7);CHECK(rd>0);CHECK(rt_cache_host_fsync_v1(rd)<0);CHECK(same(cw_file(cw_find(rd)),&id));CHECK(rt_cache_host_close_v1(rd)==0);
 int64_t v1=rt_cache_host_secure_temp_v1(r);CHECK(v1>0);CHECK(rt_cache_host_write_temp_v1(v1,0,(uint8_t*)"v1",2)==2);CHECK(rt_cache_host_publish_noreplace_v1(v1,(uint8_t*)"v1",2)==1);CHECK(rt_cache_host_close_v1(v1)<0);
 int64_t fault=rt_cache_host_secure_temp_v1(r);CHECK(fault>0);CHECK(CloseHandle(cw_file(cw_find(fault))));CHECK(rt_cache_host_publish_retained_noreplace_v2(fault,(uint8_t*)"must-not-publish",16)<0);rt_cache_host_close_v1(fault);
 CHECK(rt_cache_host_close_v1(rs)==0);CHECK(rt_cache_host_close_v1(r)==0);printf("PASS %d checks standard_user=1 same_writer=1 READ_flush_unsupported=1 receipt_unchanged=1\n",checks);return 0;}
