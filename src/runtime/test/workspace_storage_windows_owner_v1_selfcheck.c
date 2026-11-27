/* Windows SDK descriptor regression for the ACTUAL provider predicate.
 * Authored, NOT_RUN on Linux. No privileged directory ownership mutation. */
#if defined(_WIN32)
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <limits.h>
#include "runtime_workspace_storage_windows_private.h"
static unsigned checks;
#define CHECK(x) do {checks++;if(!(x)){fprintf(stderr,"FAIL:%d:%s\n",__LINE__,#x);abort();}} while(0)
int main(void) {
    BYTE system[SECURITY_MAX_SID_SIZE],foreign[SECURITY_MAX_SID_SIZE],acl_bytes[512];
    DWORD system_size=sizeof(system),foreign_size=sizeof(foreign);
    CHECK(CreateWellKnownSid(WinLocalSystemSid,NULL,system,&system_size));
    CHECK(CreateWellKnownSid(WinWorldSid,NULL,foreign,&foreign_size));
    PACL acl=(PACL)acl_bytes;CHECK(InitializeAcl(acl,sizeof(acl_bytes),ACL_REVISION));
    CHECK(AddAccessAllowedAce(acl,ACL_REVISION,FILE_ALL_ACCESS,system));
    SECURITY_DESCRIPTOR descriptor;CHECK(InitializeSecurityDescriptor(&descriptor,SECURITY_DESCRIPTOR_REVISION));
    CHECK(SetSecurityDescriptorDacl(&descriptor,TRUE,acl,FALSE));
    CHECK(SetSecurityDescriptorOwner(&descriptor,system,FALSE));
    CHECK(ws_windows_protected_descriptor_v1(&descriptor,system)==0);
    /* Same trusted-only ACL: changing ONLY the owner must now refuse. */
    CHECK(SetSecurityDescriptorOwner(&descriptor,foreign,FALSE));
    CHECK(ws_windows_protected_descriptor_v1(&descriptor,system)==EACCES);
    CHECK(SetSecurityDescriptorOwner(&descriptor,NULL,FALSE));
    CHECK(ws_windows_protected_descriptor_v1(&descriptor,system)==EACCES);
    CHECK(SetSecurityDescriptorOwner(&descriptor,system,FALSE));
    CHECK(AddAccessAllowedAce(acl,ACL_REVISION,WRITE_DAC,foreign));
    CHECK(ws_windows_protected_descriptor_v1(&descriptor,system)==EACCES);
    CHECK(SetSecurityDescriptorDacl(&descriptor,TRUE,NULL,FALSE));
    CHECK(ws_windows_protected_descriptor_v1(&descriptor,system)==EACCES);
    printf("PASS Windows storage descriptor ownership: %u checks\n",checks);return 0;
}
#else
#include <stdio.h>
int main(void){fputs("UNSUPPORTED: Windows SDK owner test requires Windows\n",stderr);return 77;}
#endif
