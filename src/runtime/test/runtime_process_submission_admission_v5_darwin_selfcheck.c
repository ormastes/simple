/* Authored live Unix-owner controls; NOT_RUN without an admitted macOS slot.
 * Reuses the existing snapshot-pin fixture, not its old test matrix. Real
 * posix_spawn/observe/reap/ack execute; only the Unix clock is substituted. */
#if !defined(__APPLE__)
int main(void) { return 77; }
#else
#define _DARWIN_C_SOURCE
#include <time.h>
#include <spawn.h>
#include <errno.h>
#include <stdint.h>
static int admission_clock_mode,admission_clock_calls,admission_spawn_count;
static int64_t admission_test_expiry;
static int admission_test_clock(clockid_t id,struct timespec* now) {
    if (clock_gettime(id,now)!=0) return -1;
    if (id!=CLOCK_REALTIME) return 0;
    admission_clock_calls++;
    if (admission_clock_mode==2 && admission_clock_calls>=2) {errno=EIO;return -1;}
    if ((admission_clock_mode==1 && admission_clock_calls>=2) ||
        (admission_clock_mode==3 && admission_clock_calls>=3)) {
        now->tv_sec=admission_test_expiry/1000;
        now->tv_nsec=(admission_test_expiry%1000)*1000000;
    }
    return 0;
}
static int admission_test_spawn(pid_t* pid,const char* path,
        const posix_spawn_file_actions_t* actions,const posix_spawnattr_t* attributes,
        char* const argv[],char* const environment[]) {
    int error=posix_spawn(pid,path,actions,attributes,argv,environment);
    if (!error) admission_spawn_count++;
    return error;
}
#define POV5_ADMISSION_CLOCK_GETTIME admission_test_clock
#define posix_spawn admission_test_spawn
#define main pov5_existing_fixture_main
#include "runtime_process_observation_v4_darwin_live_selfcheck.c"
#undef main
#undef posix_spawn

static void admission_control(const char* cwd,int64_t pin,const uint8_t digest[32],int mode) {
    struct timespec now;assert(clock_gettime(CLOCK_REALTIME,&now)==0);
    admission_test_expiry=(int64_t)now.tv_sec*1000+now.tv_nsec/1000000+10000;
    admission_clock_mode=mode;admission_clock_calls=0;admission_spawn_count=0;
    int64_t token=rt_process_observation_v4_reserve_value();assert(token>0);
    SplArray* request=request_bytes(cwd,pin,digest,"--wait-child",POV4_DESCENDANT_LEADER);
    int64_t started=rt_process_observation_v5_reserved_start_admitted_value(
        token,TEST_PIN,pin,request,admission_test_expiry);
    if (mode==1 || mode==2) {
        assert(started==-(mode==1?ETIMEDOUT:EIO));
        assert(admission_spawn_count==0);
        assert(rt_process_observation_v4_reserved_state_value(token)==3);
        assert(rt_process_observation_v5_reserved_start_admitted_value(
            token,TEST_PIN,pin,request,INT64_MAX)==-EALREADY);
    } else {
        assert(started==1 && admission_spawn_count==1);
        assert(rt_process_observation_v4_reserved_state_value(token)==4);
        assert(rt_process_observation_v4_reserved_confirm_release_value(token)==-EBUSY);
        SplArray* frozen=NULL;
        for (int turn=0;turn<300;turn++) {
            SplArray* observed=rt_process_observation_v4_reserved_observe_value(token,10000000,1);
            if (!observed) continue;
            int64_t kind=word(observed,POV4_PACKET_KIND);
            if (kind==POV4_KIND_FROZEN || kind==POV4_KIND_CLEANUP_FROZEN) {frozen=observed;break;}
            pov4_tuple4_free(observed);
        }
        assert(frozen && word(frozen,POV4_LEADER_REAPED)==1 && word(frozen,POV4_TREE_EMPTY)==1);
        SplArray* ack=rt_process_observation_v4_reserved_ack_value(token,tuple_item(frozen,2));
        assert(ack);pov4_tuple4_free(ack);pov4_tuple4_free(frozen);
    }
    assert(rt_process_observation_v4_reserved_confirm_release_value(token)==1);
    rt_array_free(request);admission_clock_mode=0;
}
int main(int argc,char** argv) {
    if (argc>1) return pov5_existing_fixture_main(argc,argv);
    char self[PATH_MAX];uint32_t length=sizeof(self);
    assert(_NSGetExecutablePath(self,&length)==0);make_snapshot(self);
    char cwd[PATH_MAX];assert(realpath(".",cwd));
    int64_t pin=rt_process_observation_v4_pin_cwd_value(cwd,strlen(cwd));assert(pin>0);
    SplArray* value=rt_process_observation_v4_cwd_digest_value(pin);uint8_t digest[32];
    assert(rt_array_bytes_copy_checked((int64_t)(uintptr_t)value,digest,32)==32);
    admission_control(cwd,pin,digest,1);admission_control(cwd,pin,digest,2);admission_control(cwd,pin,digest,3);
    assert(rt_process_observation_v4_close_cwd_value(pin)==1);rt_array_free(value);
    assert(close(snapshot_fd)==0 && unlink(snapshot_path)==0 && rmdir(snapshot_dir)==0);
    return 0;
}
#endif
