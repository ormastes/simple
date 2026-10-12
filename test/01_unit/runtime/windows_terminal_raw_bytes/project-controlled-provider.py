from pathlib import Path
import hashlib,json,argparse
parser=argparse.ArgumentParser();parser.add_argument('--owner',required=True);parser.add_argument('--out',required=True);args=parser.parse_args()
root=Path(args.out);root.mkdir(parents=True,exist_ok=True)
source=Path(args.owner).read_text()
a=source.index('int64_t rt_term_write(');b=source.index('/* Flush the terminal',a)
body=source[a:b]
# Real source body, real runtime accessors. Only OS transport has deterministic
# short/error fault injection, while successful writes still reach real OS.
prefix=r'''#define _NO_CRT_STDIO_INLINE
#include <windows.h>
#include <stdint.h>
#include <stdio.h>
#include <io.h>
extern int64_t rt_string_len(int64_t);
extern const uint8_t *rt_string_data(int64_t);
static unsigned mode,calls;
void term_test_control(unsigned value){mode=value;calls=0;}
static BOOL controlled_write(HANDLE h,const void *data,DWORD count,DWORD *written,LPOVERLAPPED overlapped){
    ++calls;
    if(mode==2){*written=0;return TRUE;}
    if(mode==3 || (mode==4&&calls>1)){*written=0;SetLastError(ERROR_WRITE_FAULT);return FALSE;}
    if((mode==1||mode==4)&&count>2)count=2;
    return WriteFile(h,data,count,written,overlapped);
}
#define WriteFile controlled_write
'''
(root/'controlled-provider.c').write_text(prefix+body)
(root/'controlled-projection.json').write_text(json.dumps({'canonical_candidate_sha256':hashlib.sha256(source.encode()).hexdigest(),'extracted_body_sha256':hashlib.sha256(body.encode()).hexdigest(),'execution':'UNEXECUTED','runtime_accessors':'real matched Rust owner; no test decoder','fault_seam':'OS WriteFile only; successful transfers reach real handle'},indent=2))
