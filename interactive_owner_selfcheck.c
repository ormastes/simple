/* Genuine child / shared-lock / transactional delivery control. UNRUN.
 * Link the actual candidate runtime, with the one process-owned TU compiled
 * with SIMPLE_RUNTIME_INTERACTIVE_V1_TEST_HOOKS. Never replace canonical
 * runtime symbols with fixture definitions. This file defines main only. */
#include "src/runtime/runtime.h"
#include "src/runtime/runtime_process_interactive_v1_abi.h"
#include <windows.h>
#include <stdio.h>
#include <string.h>

void simple_owned_interactive_v1_test_batch_gate(HANDLE,HANDLE);
void simple_owned_interactive_v1_test_created_gate(HANDLE,HANDLE);
void simple_owned_interactive_v1_test_fail_submissions(LONG);
void simple_owned_interactive_v1_test_poll_wait_gate(HANDLE,HANDLE);
int simple_owned_interactive_v1_test_input_pending(int64_t);
static int checks;
#define CHECK(x) do { checks++; if (!(x)) { fprintf(stderr,"FAIL line%d: %s\n",__LINE__,#x); return 1; } } while(0)
static char executable[32768];
static Oiv1Deadline clock_deadline(uint64_t timeout) {
    Oiv1DeadlineRequest q={1,sizeof(q),timeout}; Oiv1Deadline d; Oiv1Receipt r;
    if (simple_owned_interactive_v1_deadline(&q,sizeof(q),&d,&r,sizeof(r)) || r.status) {
        memset(&d,0,sizeof(d));
    }
    return d;
}
static int resolve(Oiv1Receipt r,int action) {
    Oiv1ResolveRequest q={1,sizeof(q),{r.ticket0,r.ticket1,r.ticket2,r.ticket3},(uint64_t)action};
    return (int)simple_owned_interactive_v1_resolve(&q,sizeof(q));
}
static Oiv1Receipt observe(int64_t h,uint8_t* out,uint8_t* err) {
    Oiv1PollRequest q={1,sizeof(q),h,clock_deadline(1000),1,{out,1024},{err,1024}}; Oiv1Receipt r;
    simple_owned_interactive_v1_poll_begin(&q,sizeof(q),&r,sizeof(r)); return r;
}
static Oiv1Receipt start_peer(const char* mode,const char* argument,uint64_t timeout) {
    Oiv1ConstSpan args[2]={{(const uint8_t*)mode,strlen(mode)},
        {(const uint8_t*)argument,argument?strlen(argument):0}};
    Oiv1StartRequest q={1,sizeof(q),{(const uint8_t*)executable,strlen(executable)},
        {args,argument?2:1},clock_deadline(timeout),65536,4096,4096,0}; Oiv1Receipt r;
    simple_owned_interactive_v1_start_begin(&q,sizeof(q),&r,sizeof(r)); return r;
}
static int clean_peer(int64_t handle) {
    Oiv1ControlRequest q={1,sizeof(q),handle,clock_deadline(5000),0}; Oiv1Receipt r;
    for (int i=0;i<5000 && (uint64_t)q.deadline.expires_ms>GetTickCount64();i++) {
        simple_owned_interactive_v1_cancel(&q,sizeof(q),&r,sizeof(r));
        if (r.flags&OIV1_FLAG_CANCELREQUESTED) break; Sleep(1);
    }
    if (!(r.flags&OIV1_FLAG_CANCELREQUESTED)) return 1;
    q.flags=1; /* Explicit abort path permits measured unread-byte discard. */
    for (int i=0;i<5000;i++) {
        if ((uint64_t)q.deadline.expires_ms<=GetTickCount64()) return 1;
        simple_owned_interactive_v1_collect(&q,sizeof(q),&r,sizeof(r));
        if (r.phase==OIV1_PHASE_COLLECTED) {
            Oiv1ReleaseRequest release={1,sizeof(release),handle};
            simple_owned_interactive_v1_release(&release,sizeof(release),&r,sizeof(r));
            if ((r.validity_mask&OIV1_VALID_PHASE) && r.phase==OIV1_PHASE_RELEASED) return 0;
            if (r.status!=OIV1_STATUS_BUSY && r.status!=OIV1_STATUS_NOTREADY &&
                r.status!=OIV1_STATUS_RETAINEDCLEANUP) return 1;
            /* Collected can precede final worker pin drops. Keep the SAME
             * cleanup deadline and retry legitimate deferred retirement. */
        }
        Sleep(1);
    }
    return 1;
}
static int admission_controls(void) {
    /* NULL+zero is a valid raw empty span. The actual child must receive an
     * empty argument, preserving counted-span semantics through argv quoting. */
    Oiv1ConstSpan empty_args[2]={{(const uint8_t*)"--empty-argument-child",22},{NULL,0}};
    Oiv1StartRequest empty_request={1,sizeof(empty_request),{(const uint8_t*)executable,strlen(executable)},
        {empty_args,2},clock_deadline(5000),64,4096,4096,0}; Oiv1Receipt empty;
    simple_owned_interactive_v1_start_begin(&empty_request,sizeof(empty_request),&empty,sizeof(empty));
    CHECK(empty.validity_mask&OIV1_VALID_OWNER); CHECK(resolve(empty,1)==0);
    int64_t empty_handle=empty.handle_echo;
    uint8_t empty_out[1024],empty_err[1024];
    for (int i=0;i<5000;i++) {
        empty=observe(empty_handle,empty_out,empty_err);
        if (empty.exit_kind==OIV1_EXIT_EXITED) break; Sleep(1);
    }
    CHECK(empty.exit_kind==OIV1_EXIT_EXITED && empty.exit_value==0); CHECK(clean_peer(empty_handle)==0);
    /* Negative executor injection is not a positive process-launch oracle. */
    simple_owned_interactive_v1_test_fail_submissions(130);
    for (int i=0;i<130;i++) {
        Oiv1Receipt failed=start_peer("--legacy-child",NULL,5000);
        CHECK(failed.phase==OIV1_PHASE_FAILEDHELD && (failed.flags&OIV1_FLAG_NOCHILDPROVEN));
        CHECK(resolve(failed,2)==OIV1_RESOLVE_RECORDED);
        Oiv1ReleaseRequest q={1,sizeof(q),failed.handle_echo}; Oiv1Receipt retired;
        simple_owned_interactive_v1_release(&q,sizeof(q),&retired,sizeof(retired));
        CHECK(retired.status==OIV1_STATUS_STALE); /* same-owner maintenance reclaimed it */
    }
    simple_owned_interactive_v1_test_fail_submissions(0);
    WCHAR directory[32768],marker[32768]; char marker_utf8[32768];
    CHECK(GetTempPathW(32768,directory)>0); CHECK(GetTempFileNameW(directory,L"siv",0,marker)>0);
    CHECK(DeleteFileW(marker));
    CHECK(WideCharToMultiByte(CP_UTF8,WC_ERR_INVALID_CHARS,marker,-1,marker_utf8,sizeof(marker_utf8),NULL,NULL)>0);
    for (int cancel=0;cancel<2;cancel++) {
        HANDLE entered=CreateEventW(NULL,TRUE,FALSE,NULL),release=CreateEventW(NULL,TRUE,FALSE,NULL);
        CHECK(entered && release); simple_owned_interactive_v1_test_created_gate(entered,release);
        Oiv1Receipt start=start_peer("--marker-child",marker_utf8,2000);
        CHECK(start.validity_mask&OIV1_VALID_OWNER); CHECK(resolve(start,1)==0);
        CHECK(WaitForSingleObject(entered,5000)==WAIT_OBJECT_0);
        CHECK(GetFileAttributesW(marker)==INVALID_FILE_ATTRIBUTES && GetLastError()==ERROR_FILE_NOT_FOUND);
        if (cancel) {
            Oiv1ControlRequest q={1,sizeof(q),start.handle_echo,clock_deadline(5000),0}; Oiv1Receipt receipt;
            simple_owned_interactive_v1_cancel(&q,sizeof(q),&receipt,sizeof(receipt));
            CHECK(receipt.flags&OIV1_FLAG_CANCELREQUESTED);
            uint8_t byte=1; Oiv1WriteRequest write={1,sizeof(write),start.handle_echo,{&byte,1},0,1,0,clock_deadline(5000)};
            simple_owned_interactive_v1_write_some(&write,sizeof(write),&receipt,sizeof(receipt));
            CHECK(receipt.accepted_delta==0);
        } else {
            /* A genuine delayed CreateProcess returned a suspended child;
             * wait past ORIGINAL startup deadline before releasing the gate. */
            Sleep(2100);
        }
        SetEvent(release);
        if (!cancel) {
            uint8_t output[1024],error[1024]; Oiv1Receipt expired;
            for (int i=0;i<5000;i++) { expired=observe(start.handle_echo,output,error);
                if (expired.flags&OIV1_FLAG_TIMEDOUT) break; Sleep(1); }
            CHECK(expired.flags&OIV1_FLAG_TIMEDOUT);
            CHECK(!(expired.flags&OIV1_FLAG_NOCHILDPROVEN)); /* actual suspended child existed */
        }
        CHECK(clean_peer(start.handle_echo)==0);
        CHECK(GetFileAttributesW(marker)==INVALID_FILE_ATTRIBUTES && GetLastError()==ERROR_FILE_NOT_FOUND);
        simple_owned_interactive_v1_test_created_gate(NULL,NULL); CloseHandle(entered); CloseHandle(release);
    }
    /* Positive marker control proves the same real child would execute. */
    Oiv1Receipt live=start_peer("--marker-child",marker_utf8,5000);
    CHECK(live.validity_mask&OIV1_VALID_OWNER); CHECK(resolve(live,1)==0);
    for (int i=0;i<5000 && GetFileAttributesW(marker)==INVALID_FILE_ATTRIBUTES;i++) Sleep(1);
    CHECK(GetFileAttributesW(marker)!=INVALID_FILE_ATTRIBUTES); CHECK(clean_peer(live.handle_echo)==0); CHECK(DeleteFileW(marker));
    return 0;
}
static int pressure_cancel_control(void) {
    Oiv1Receipt start=start_peer("--write-pressure-child",NULL,5000);
    CHECK(start.validity_mask&OIV1_VALID_OWNER); CHECK(resolve(start,1)==0);
    uint8_t output[1024],error[1024],data[4096]; memset(data,0x5a,sizeof(data)); Oiv1Receipt receipt;
    for (int i=0;i<5000;i++) {
        receipt=observe(start.handle_echo,output,error);
        if (receipt.stdout_count) { CHECK(receipt.stdout_count==5 && !memcmp(output,"ready",5)); CHECK(resolve(receipt,1)==0); break; }
        Sleep(1);
    }
    uint64_t accepted=0,written=0; int pending=0;
    for (int i=0;i<500;i++) {
        Oiv1WriteRequest q={1,sizeof(q),start.handle_echo,{data,sizeof(data)},0,4096,accepted,clock_deadline(5000)};
        simple_owned_interactive_v1_write_some(&q,sizeof(q),&receipt,sizeof(receipt));
        if (receipt.status==OIV1_STATUS_BUSY) { Sleep(1); continue; }
        CHECK(receipt.validity_mask&OIV1_VALID_COUNTS);
        CHECK(receipt.accepted_total==accepted+receipt.accepted_delta);
        CHECK(receipt.written_total>=written && receipt.written_total<=receipt.accepted_total);
        accepted=receipt.accepted_total; written=receipt.written_total;
        pending=simple_owned_interactive_v1_test_input_pending(start.handle_echo);
        if (pending==1 && written>0 && receipt.stdin_queued>0) break;
        Sleep(1);
    }
    CHECK(pending==1 && written>0 && accepted>written);
    Oiv1ControlRequest cancel={1,sizeof(cancel),start.handle_echo,clock_deadline(5000),0};
    for (int i=0;i<5000;i++) {
        simple_owned_interactive_v1_cancel(&cancel,sizeof(cancel),&receipt,sizeof(receipt));
        if (receipt.flags&OIV1_FLAG_CANCELREQUESTED) break; Sleep(1);
    }
    CHECK(receipt.flags&OIV1_FLAG_CANCELREQUESTED);
    Oiv1WriteRequest after={1,sizeof(after),start.handle_echo,{data,1},0,1,accepted,clock_deadline(5000)};
    simple_owned_interactive_v1_write_some(&after,sizeof(after),&receipt,sizeof(receipt)); CHECK(receipt.accepted_delta==0);
    for (int i=0;i<5000;i++) {
        receipt=observe(start.handle_echo,output,error);
        if (receipt.status==OIV1_STATUS_BUSY) { Sleep(1); continue; }
        CHECK(receipt.validity_mask&OIV1_VALID_OWNER);
        CHECK(receipt.accepted_total==accepted && receipt.written_total>=written && receipt.written_total<=accepted);
        if (receipt.flags&OIV1_FLAG_LOANPRESENT) CHECK(resolve(receipt,1)==0);
        if (!(receipt.validity_mask&OIV1_VALID_COUNTS)) CHECK(receipt.stdin_state==OIV1_STREAM_FAILED);
        if (receipt.exit_kind==OIV1_EXIT_EXITED) break; Sleep(1);
    }
    CHECK(receipt.exit_kind==OIV1_EXIT_EXITED); CHECK(clean_peer(start.handle_echo)==0); return 0;
}
typedef struct PollThread { Oiv1PollRequest request; Oiv1Receipt receipt; } PollThread;
static DWORD WINAPI poll_thread(void* argument) {
    PollThread* context=(PollThread*)argument;
    do {
        simple_owned_interactive_v1_poll_begin(&context->request,sizeof(context->request),&context->receipt,sizeof(context->receipt));
        if (context->receipt.status!=OIV1_STATUS_BUSY) break; Sleep(1);
    } while ((uint64_t)context->request.deadline.expires_ms>GetTickCount64());
    return 0;
}
static int post_wait_deadline_control(void) {
    char name[100],go_name[110],wrote_name[110];
    _snprintf(name,sizeof(name),"Local\\simple-deadline-%lu-%llu",GetCurrentProcessId(),(unsigned long long)GetTickCount64());
    _snprintf(go_name,sizeof(go_name),"%s-go",name); _snprintf(wrote_name,sizeof(wrote_name),"%s-wrote",name);
    HANDLE go=CreateEventA(NULL,TRUE,FALSE,go_name); CHECK(go && GetLastError()!=ERROR_ALREADY_EXISTS);
    HANDLE wrote=CreateEventA(NULL,TRUE,FALSE,wrote_name); CHECK(wrote && GetLastError()!=ERROR_ALREADY_EXISTS);
    Oiv1Receipt start=start_peer("--deadline-child",name,5000); CHECK(start.validity_mask&OIV1_VALID_OWNER); CHECK(resolve(start,1)==0);
    uint8_t out[1024],err[1024]; Oiv1Receipt r;
    for (int i=0;i<5000;i++) {
        r=observe(start.handle_echo,out,err);
        if (r.stdout_count) { CHECK(r.stdout_count==5 && !memcmp(out,"ready",5)); CHECK(resolve(r,1)==0); break; }
        Sleep(1);
    }
    uint8_t ack=1; Oiv1WriteRequest write={1,sizeof(write),start.handle_echo,{&ack,1},0,1,0,clock_deadline(5000)};
    for (int i=0;i<5000;i++) {
        simple_owned_interactive_v1_write_some(&write,sizeof(write),&r,sizeof(r));
        if (r.status!=OIV1_STATUS_BUSY) break; Sleep(1);
    }
    CHECK(r.accepted_delta==1);
    HANDLE entered=CreateEventW(NULL,TRUE,FALSE,NULL),release=CreateEventW(NULL,TRUE,FALSE,NULL); CHECK(entered && release);
    simple_owned_interactive_v1_test_poll_wait_gate(entered,release);
    PollThread poll={{1,sizeof(Oiv1PollRequest),start.handle_echo,clock_deadline(100),100,{out,sizeof(out)},{err,sizeof(err)}},{0}};
    HANDLE thread=CreateThread(NULL,0,poll_thread,&poll,0,NULL); CHECK(thread);
    CHECK(WaitForSingleObject(entered,5000)==WAIT_OBJECT_0);
    SetEvent(go); CHECK(WaitForSingleObject(wrote,5000)==WAIT_OBJECT_0);
    while ((uint64_t)poll.request.deadline.expires_ms>GetTickCount64()) Sleep(1);
    SetEvent(release); CHECK(WaitForSingleObject(thread,5000)==WAIT_OBJECT_0); r=poll.receipt;
    simple_owned_interactive_v1_test_poll_wait_gate(NULL,NULL); CloseHandle(thread); CloseHandle(entered); CloseHandle(release);
    CHECK(r.status==OIV1_STATUS_DEADLINEREACHED && (r.flags&OIV1_FLAG_OBSERVEDBEFOREWAIT));
    CHECK(r.stdout_count==0 && !(r.flags&OIV1_FLAG_LOANPRESENT));
    int received=0;
    for (int i=0;i<5000;i++) {
        r=observe(start.handle_echo,out,err);
        if (r.stdout_count) { CHECK(r.stdout_count==4 && !memcmp(out,"late",4)); CHECK(resolve(r,1)==0); received++; }
        if (r.exit_kind==OIV1_EXIT_EXITED && r.stdout_state==OIV1_STREAM_EOF) break; Sleep(1);
    }
    CHECK(received==1 && r.exit_kind==OIV1_EXIT_EXITED && r.exit_value==0); CHECK(clean_peer(start.handle_echo)==0);
    CloseHandle(go); CloseHandle(wrote); return 0;
}
static DWORD WINAPI legacy_start(void* result) {
    const char* args[]={executable,"--legacy-child",NULL}; RtOwnedProcessTokenV2 token;
    RtOwnedProcessStartReceiptV2 receipt;
    *(int*)result=0;
    if (rt_process_owned_start_v3(executable,args,NULL,0,2000,100,1024,&token,&receipt)) {
        RtOwnedProcessResultV2 terminal; memset(&terminal,0,sizeof(terminal));
        for (int i=0;i<500;i++) {
            if (rt_process_owned_collect_v2(token,&terminal)) {
                *(int*)result=terminal.reaped && terminal.exit_code==0 && !terminal.runtime_error; break;
            }
            Sleep(1);
        }
    }
    return 0;
}
int main(int argc,char** argv) {
    if (argc>=2 && !strcmp(argv[1],"--empty-argument-child"))
        return argc==3 && argv[2][0]==0?0:16;
    if (argc==2 && !strcmp(argv[1],"--legacy-child")) return 0;
    if (argc==2 && !strcmp(argv[1],"--write-pressure-child")) {
        DWORD n=0; WriteFile(GetStdHandle(STD_OUTPUT_HANDLE),"ready",5,&n,NULL); Sleep(300);
        for (;;) { uint8_t byte; if (!ReadFile(GetStdHandle(STD_INPUT_HANDLE),&byte,1,&n,NULL) || !n) return 0; Sleep(2); }
    }
    if (argc==3 && !strcmp(argv[1],"--deadline-child")) {
        char go_name[110],wrote_name[110]; _snprintf(go_name,sizeof(go_name),"%s-go",argv[2]); _snprintf(wrote_name,sizeof(wrote_name),"%s-wrote",argv[2]);
        HANDLE go=OpenEventA(SYNCHRONIZE,FALSE,go_name),wrote=OpenEventA(EVENT_MODIFY_STATE,FALSE,wrote_name); if (!go || !wrote) return 14;
        DWORD n=0; WriteFile(GetStdHandle(STD_OUTPUT_HANDLE),"ready",5,&n,NULL); uint8_t ack;
        if (!ReadFile(GetStdHandle(STD_INPUT_HANDLE),&ack,1,&n,NULL) || n!=1) return 12;
        if (WaitForSingleObject(go,5000)!=WAIT_OBJECT_0) return 15;
        int ok=WriteFile(GetStdHandle(STD_OUTPUT_HANDLE),"late",4,&n,NULL)!=0 && n==4;
        if (ok) SetEvent(wrote); CloseHandle(go); CloseHandle(wrote); return ok?0:13;
    }
    if (argc==3 && !strcmp(argv[1],"--marker-child")) {
        WCHAR marker[32768];
        if (!MultiByteToWideChar(CP_UTF8,MB_ERR_INVALID_CHARS,argv[2],-1,marker,32768)) return 9;
        HANDLE file=CreateFileW(marker,GENERIC_WRITE,0,NULL,CREATE_NEW,FILE_ATTRIBUTE_NORMAL,NULL);
        if (file==INVALID_HANDLE_VALUE) return 10;
        DWORD n=0; int ok=WriteFile(file,"executed",8,&n,NULL)!=0 && n==8; CloseHandle(file); return ok?0:11;
    }
    if (argc==2 && !strcmp(argv[1],"--interactive-child")) {
        const uint8_t output[]={0xff,0,0x80,'r','e','a','d','y'};
        DWORD n=0; WriteFile(GetStdHandle(STD_OUTPUT_HANDLE),output,sizeof(output),&n,NULL);
        WriteFile(GetStdHandle(STD_ERROR_HANDLE),"noise!",6,&n,NULL);
        uint8_t input[4]; DWORD got=0;
        while (got<4) { DWORD one=0;
            if (!ReadFile(GetStdHandle(STD_INPUT_HANDLE),input+got,4-got,&one,NULL) || !one) return 7;
            got+=one;
        }
        if (memcmp(input,"ACK\n",4)) return 8;
        WriteFile(GetStdHandle(STD_OUTPUT_HANDLE),"Content-Length: 2\r\n\r\n{}",23,&n,NULL);
        return 0;
    }
    /* A malformed child mode can never fall through into the parent campaign. */
    if (argc!=1) return 17;
    WCHAR wide[32768]; CHECK(GetModuleFileNameW(NULL,wide,32768)>0);
    CHECK(WideCharToMultiByte(CP_UTF8,WC_ERR_INVALID_CHARS,wide,-1,executable,sizeof(executable),NULL,NULL)>0);
    CHECK(admission_controls()==0);
    CHECK(pressure_cancel_control()==0);
    CHECK(post_wait_deadline_control()==0);
    Oiv1ConstSpan args={(const uint8_t*)"--interactive-child",19};
    Oiv1StartRequest start={1,sizeof(start),{(const uint8_t*)executable,strlen(executable)},
        {&args,1},clock_deadline(5000),64,4096,4096,0}; Oiv1Receipt begun;
    CHECK(simple_owned_interactive_v1_start_begin(&start,sizeof(start),&begun,sizeof(begun))==0);
    CHECK((begun.validity_mask&OIV1_VALID_OWNER) && begun.phase==OIV1_PHASE_STARTING);
    CHECK(resolve(begun,1)==OIV1_RESOLVE_RECORDED);
    int64_t h=begun.handle_echo; uint8_t out[1024],err[1024]; Oiv1Receipt ready;
    size_t noise_n=0;
    for (int i=0;i<5000;i++) {
        ready=observe(h,out,err);
        if (ready.stdout_count) break;
        if (ready.flags&OIV1_FLAG_LOANPRESENT) {
            CHECK(ready.stderr_count==6 && !memcmp(err,"noise!",6));
            noise_n+=(size_t)ready.stderr_count; CHECK(resolve(ready,1)==0);
        }
        Sleep(1);
    }
    /* Reserve real output before the legacy lock is stalled. */
    CHECK(ready.phase==OIV1_PHASE_RUNNING);
    CHECK(ready.flags&OIV1_FLAG_LOANPRESENT);
    const uint8_t expected_raw[]={0xff,0,0x80,'r','e','a','d','y'};
    CHECK(ready.stdout_count==sizeof(expected_raw) && !memcmp(out,expected_raw,sizeof(expected_raw)));
    if (ready.stderr_count) { CHECK(ready.stderr_count==6 && !memcmp(err,"noise!",6)); noise_n+=6; }
    HANDLE entered=CreateEventW(NULL,TRUE,FALSE,NULL),release=CreateEventW(NULL,TRUE,FALSE,NULL);
    CHECK(entered && release); simple_owned_interactive_v1_test_batch_gate(entered,release);
    int legacy_ok=0; HANDLE thread=CreateThread(NULL,0,legacy_start,&legacy_ok,0,NULL); CHECK(thread);
    CHECK(WaitForSingleObject(entered,5000)==WAIT_OBJECT_0);
    ULONGLONG before=GetTickCount64(); Oiv1Receipt busy=observe(h,out,err);
    CHECK(GetTickCount64()-before<100); CHECK(busy.status==OIV1_STATUS_BUSY && busy.validity_mask==0);
    Oiv1WriteRequest write={1,sizeof(write),h,{(const uint8_t*)"ACK\n",4},0,4,0,clock_deadline(1000)};
    simple_owned_interactive_v1_write_some(&write,sizeof(write),&busy,sizeof(busy));
    CHECK(busy.status==OIV1_STATUS_BUSY && busy.accepted_delta==0 && busy.validity_mask==0);
    Oiv1ControlRequest control={1,sizeof(control),h,clock_deadline(1000),0};
    simple_owned_interactive_v1_cancel(&control,sizeof(control),&busy,sizeof(busy)); CHECK(busy.status==OIV1_STATUS_BUSY);
    simple_owned_interactive_v1_close_stdin(&control,sizeof(control),&busy,sizeof(busy)); CHECK(busy.status==OIV1_STATUS_BUSY);
    simple_owned_interactive_v1_collect(&control,sizeof(control),&busy,sizeof(busy)); CHECK(busy.status==OIV1_STATUS_BUSY);
    Oiv1ReleaseRequest retire={1,sizeof(retire),h};
    simple_owned_interactive_v1_release(&retire,sizeof(retire),&busy,sizeof(busy)); CHECK(busy.status==OIV1_STATUS_BUSY);
    CHECK(resolve(ready,1)==0); CHECK(resolve(ready,1)==1); CHECK(resolve(ready,2)==2);
    SetEvent(release); CHECK(WaitForSingleObject(thread,5000)==WAIT_OBJECT_0); CHECK(legacy_ok);
    simple_owned_interactive_v1_test_batch_gate(NULL,NULL);
    CloseHandle(thread); CloseHandle(entered); CloseHandle(release);
    /* Re-observation cannot replay the committed raw prefix. */
    Oiv1Receipt next=observe(h,out,err); CHECK(next.stdout_count==0);
    if (next.flags&OIV1_FLAG_LOANPRESENT) {
        CHECK(next.stderr_count==6 && !memcmp(err,"noise!",6)); noise_n+=6; CHECK(resolve(next,1)==0);
    }
    write.deadline=clock_deadline(1000);
    for (int i=0;i<5000;i++) {
        simple_owned_interactive_v1_write_some(&write,sizeof(write),&next,sizeof(next));
        if (next.status!=OIV1_STATUS_BUSY) break; Sleep(1);
    }
    CHECK(next.accepted_delta==4 && next.accepted_total==4);
    uint8_t framed[64]; size_t framed_n=0;
    for (int i=0;i<5000;i++) {
        next=observe(h,out,err);
        if (next.flags&OIV1_FLAG_LOANPRESENT) {
            CHECK(framed_n+next.stdout_count<=sizeof(framed));
            memcpy(framed+framed_n,out,(size_t)next.stdout_count); framed_n+=(size_t)next.stdout_count;
            if (next.stderr_count) { CHECK(next.stderr_count==6 && !memcmp(err,"noise!",6)); noise_n+=6; }
            CHECK(resolve(next,1)==0);
        }
        if (next.exit_kind==OIV1_EXIT_EXITED && next.stdout_state==OIV1_STREAM_EOF && next.stderr_state==OIV1_STREAM_EOF) break;
        Sleep(1);
    }
    CHECK(next.exit_kind==OIV1_EXIT_EXITED && next.exit_value==0);
    CHECK(next.stdout_state==OIV1_STREAM_EOF && next.stderr_state==OIV1_STREAM_EOF);
    CHECK(noise_n==6);
    CHECK(framed_n==23 && !memcmp(framed,"Content-Length: 2\r\n\r\n{}",23));
    control.deadline=clock_deadline(5000);
    for (int i=0;i<5000 && (uint64_t)control.deadline.expires_ms>GetTickCount64();i++) {
        simple_owned_interactive_v1_collect(&control,sizeof(control),&next,sizeof(next));
        if (next.phase==OIV1_PHASE_COLLECTED) break; Sleep(1);
    }
    CHECK(next.phase==OIV1_PHASE_COLLECTED);
    simple_owned_interactive_v1_release(&retire,sizeof(retire),&next,sizeof(next)); CHECK(next.phase==OIV1_PHASE_RELEASED);
    CHECK(resolve(ready,1)==OIV1_RESOLVE_STALE);
    next=observe(h,out,err); CHECK(next.status==OIV1_STATUS_STALE);
    printf("interactive-owner checks=%d PASS\n",checks); return 0;
}
