/* AUTHORED_UNRUN. Includes the actual owner/parser with symbol aliases only;
 * no registry injection, fake native success or kernel qualification. Link with
 * real Core-C runtime. These vectors test notes framing and refusal only. */
#define _GNU_SOURCE
#include "runtime.h"
#include "runtime_workspace_storage_v1.h"
#include <stdio.h>
#include <string.h>
#define rt_workspace_storage_open_v1 kernel_fixture_open_v1
#define rt_workspace_storage_recover_v1 kernel_fixture_recover_v1
#define rt_workspace_storage_observe_v1 kernel_fixture_observe_v1
#define rt_workspace_storage_release_if_absent_v1 kernel_fixture_release_v1
#define rt_workspace_storage_forget_released_v1 kernel_fixture_forget_v1
#define rt_linux_container_user_open_v1 kernel_fixture_user_open_v1
#define rt_linux_container_user_observe_v1 kernel_fixture_user_observe_v1
#define rt_linux_container_user_close_v1 kernel_fixture_user_close_v1
#define rt_workspace_storage_prepare_executable_v1 kernel_fixture_prepare_v1
#define rt_linux_container_containment_capture_v1 kernel_fixture_capture_v1
#define rt_linux_container_containment_observe_v1 kernel_fixture_contain_observe_v1
#define rt_linux_container_containment_close_v1 kernel_fixture_close_v1
#define rt_linux_container_containment_kernel_observe_v1 kernel_fixture_kernel_observe_v1
#include "../runtime_workspace_storage_v1.c"
static unsigned checks;
#define CHECK(x) do {checks++;if(!(x)){fprintf(stderr,"kernel observer check %u line %d failed\n",checks,__LINE__);return 1;}}while(0)
int main(void){
#if !defined(__linux__)
    fprintf(stderr,"Linux Core-C fixture required\n");return 77;
#else
    uint8_t notes[40]={0};uint32_t words[]={4,4,3};char id[129];
    memcpy(notes,words,12);memcpy(notes+12,"GNU\0",4);
    notes[16]=1;notes[17]=2;notes[18]=3;notes[19]=4;
    CHECK(ws_kernel_notes_parse_v1(notes,20,id)==0&&!strcmp(id,"01020304"));
    CHECK(ws_kernel_notes_parse_v1(notes,19,id)!=0);
    CHECK(ws_kernel_notes_parse_v1(notes,11,id)!=0);
    memcpy(notes+20,notes,20);CHECK(ws_kernel_notes_parse_v1(notes,40,id)!=0);
    uint32_t large=UINT32_MAX;memcpy(notes+4,&large,4);CHECK(ws_kernel_notes_parse_v1(notes,20,id)!=0);
    uint32_t zero=0;memcpy(notes+4,&zero,4);CHECK(ws_kernel_notes_parse_v1(notes,16,id)!=0);
    CHECK(ws_kernel_hex_v1("ab")&&ws_kernel_hex_v1("0123456789abcdef"));
    CHECK(!ws_kernel_hex_v1("a")&&!ws_kernel_hex_v1("AB")&&!ws_kernel_hex_v1("ag"));
    CHECK(ws_kernel_release_v1("6.12.0-installed")&&!ws_kernel_release_v1("6.12/source"));
    int64_t digest=rt_string_new((const uint8_t*)"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",64);
    int64_t release=rt_string_new((const uint8_t*)"6.12.0-installed",16),build=rt_string_new((const uint8_t*)"ab",2);
    CHECK(rt_string_len(kernel_fixture_kernel_observe_v1(0,digest,release,build,digest))==0);
    CHECK(rt_string_len(kernel_fixture_kernel_observe_v1(INT64_MAX,digest,release,build,digest))==0);
    printf("kernel observer negative/parser checks=%u; no running-kernel qualification\n",checks);return 0;
#endif
}
