/* Build as a real static ELF: the production sealed-image pin rejects dynamic ELF.
 * This helper has no test authority over the parent owner or receipt fields. */
#include <unistd.h>
#include <string.h>
int main(int argc,char** argv) {
    if(argc==2&&strcmp(argv[1],"hold")==0)for(;;)pause();
    return write(1,"exec-v6\n",8)==8?0:12;
}
