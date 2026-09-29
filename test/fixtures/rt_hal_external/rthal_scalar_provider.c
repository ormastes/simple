/* Test-only C comparator for the frozen rthal-scalar-v2 process protocol.
 * Pure Simple owns execution and effects, but this child independently derives
 * its result so a wrong Pure oracle is falsifiable.  For lane i in 0..3:
 *
 *   base = op[i] XOR rotl(input[(i+1)%4], 7+11*i)
 *          XOR (GOLDEN + FNV_PRIME*i)
 *   replay: base ^= rotl(pure_trace[(i+2)%4], 13+7*i) XOR EFFECT_DOMAIN
 *   outcome[i] = mix64(base)
 *   error[i] = 0
 *   query trace[i] = mix64(base XOR TRACE_DOMAIN)
 *   replay trace[i] = pure_trace[i]
 *
 * mix64 is the SplitMix64 finalizer.  All arithmetic is wrapping u64.  Query
 * mode receives no expected outcome/error/trace fields; replay receives only
 * trace as its effect-replay input. Work and storage are fixed O(1), with no
 * heap allocation. */
#include <errno.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { QUERY_ARGC = 13, REPLAY_ARGC = 17 };
enum { IO_CAP = 1048576, IO_HEADER = 32, IO_TYPE_FIXED = 56 };
static unsigned char io_req[IO_CAP], io_eff[IO_CAP], io_out[IO_CAP];
/* Installed once at process startup by the cold provider plan.  Worker input
 * can select no new operation or adapter. */
static const char *registered_operation = NULL;
static unsigned registered_adapter = 0;
static int64_t recorded_case = -1, recorded_schema = -1;
static uint32_t rd32(const unsigned char *p){return (uint32_t)p[0]|(uint32_t)p[1]<<8|(uint32_t)p[2]<<16|(uint32_t)p[3]<<24;}
static uint64_t rd64(const unsigned char *p){uint64_t v=0;for(unsigned i=0;i<8;i++)v|=(uint64_t)p[i]<<(8*i);return v;}
static void wr64(unsigned char *p,uint64_t v){for(unsigned i=0;i<8;i++)p[i]=(unsigned char)(v>>(8*i));}
static int grow(size_t *p,size_t n,size_t cap){if(n>cap-*p)return 0;*p+=n;return 1;}
static int hx(int c){return c>='0'&&c<='9'?c-'0':c>='a'&&c<='f'?c-'a'+10:-1;}
static int readhex(unsigned char *p,size_t n){if(n>IO_CAP||n>SIZE_MAX/2)return 0;for(size_t i=0;i<n;i++){int a=hx(getchar()),b=hx(getchar());if(a<0||b<0)return 0;p[i]=(unsigned char)(a*16+b);}return 1;}
static int writehex(const unsigned char*p,size_t n){static const char d[]="0123456789abcdef";for(size_t i=0;i<n;i++)if(putchar(d[p[i]>>4])<0||putchar(d[p[i]&15])<0)return 0;return 1;}
static int append(size_t *o,const void*p,size_t n){if(!grow(o,n,IO_CAP))return 0;memcpy(io_out+*o-n,p,n);return 1;}
static int append64(size_t *o,uint64_t v){if(!grow(o,8,IO_CAP))return 0;wr64(io_out+*o-8,v);return 1;}
static int transcript_ok(const unsigned char*p,size_t events,uint64_t domain){
    return events>=2&&events<=IO_CAP/16&&rd64(p)==1&&rd64(p+8)>>32==domain&&rd64(p+(events-1)*16)==2;
}
static int unit_descriptor(const unsigned char *p,size_t n){
    static const unsigned char unit[]={'v','2',';','u','n','i','t'};
    return n==sizeof unit&&!memcmp(p,unit,sizeof unit);
}
static int unit_stream(size_t *o,uint64_t domain){
    return append64(o,6)&&append64(o,3)&&append64(o,0)&&append64(o,1)&&append64(o,domain<<32)&&append64(o,11)&&append64(o,0)&&append64(o,2)&&append64(o,0);
}
static int descriptor_is(const unsigned char *p,size_t n,const char *s){size_t m=strlen(s);return n==m&&!memcmp(p,s,m);}
static int text_events(const unsigned char*p,size_t n,size_t payload,uint64_t domain){
    return n==64&&rd64(p)==1&&rd64(p+8)>>32==domain&&rd64(p+16)==25&&rd64(p+24)==payload&&rd64(p+32)==26&&rd64(p+40)==0&&rd64(p+48)==2&&rd64(p+56)==0;
}
static int bytes_events(const unsigned char*p,size_t n,size_t payload,uint64_t domain){
    return n==64&&rd64(p)==1&&rd64(p+8)>>32==domain&&rd64(p+16)==23&&rd64(p+24)==payload&&rd64(p+32)==24&&rd64(p+40)==0&&rd64(p+48)==2&&rd64(p+56)==0;
}
static int canonical_utf8_identity(const unsigned char *p,size_t n){
    if(!p||!n)return 0;
    for(size_t i=0;i<n;){unsigned c=p[i];if(!c)return 0;
        if(c<=0x7f){i++;continue;}size_t more;unsigned lo=0x80,hi=0xbf;
        if(c>=0xc2&&c<=0xdf)more=1;
        else if(c>=0xe0&&c<=0xef){more=2;if(c==0xe0)lo=0xa0;if(c==0xed)hi=0x9f;}
        else if(c>=0xf0&&c<=0xf4){more=3;if(c==0xf0)lo=0x90;if(c==0xf4)hi=0x8f;}
        else return 0;
        if(more>n-i-1||p[i+1]<lo||p[i+1]>hi)return 0;
        for(size_t j=2;j<=more;j++)if(p[i+j]<0x80||p[i+j]>0xbf)return 0;
        i+=more+1;
    }return 1;
}
/* HIO2 V2 is the typed operation request.  Its UTF-8 operation identity,
 * input descriptor, input transcript and input payload select this bounded
 * native registry.  It is never a Pure termination receipt or seed. */
static int provider_unknown(void){fputs("RTHAL-PROVIDER-E-UNKNOWN-OP\n",stderr);return 78;}
static int execute_idempotent_record(const unsigned char *req){
    int64_t case_id=(int64_t)rd64(req+8),schema=(int64_t)rd64(req+24);
    if(case_id<0||schema<=0)return 0;
    if((recorded_case>=0&&recorded_case!=case_id)||(recorded_schema>=0&&recorded_schema!=schema))return 0;
    recorded_case=case_id;recorded_schema=schema;return 1;
}
typedef struct {const unsigned char*p;size_t n;} env_span;
typedef struct {env_span id;env_span path;env_span hash;} env_tool;
typedef struct {env_span id;env_span schema;int64_t args,timeout,out,err;} env_probe;
static int env_span_eq(env_span a,env_span b){return a.n==b.n&&!memcmp(a.p,b.p,a.n);}
static int env_has_control(env_span v){for(size_t i=0;i<v.n;i++)if(v.p[i]<32||v.p[i]==127)return 1;return 0;}
static int env_contains(env_span v,const char*s){size_t n=strlen(s);if(!n||n>v.n)return 0;for(size_t i=0;i+n<=v.n;i++)if(!memcmp(v.p+i,s,n))return 1;return 0;}
static int env_has_byte(env_span v,unsigned char c){for(size_t i=0;i<v.n;i++)if(v.p[i]==c)return 1;return 0;}
static int env_blank(env_span v){for(size_t i=0;i<v.n;i++)if(v.p[i]!=' ')return 0;return 1;}
static int env_starts(env_span v,const char*s){size_t n=strlen(s);return n<=v.n&&!memcmp(v.p,s,n);}
static int env_ends(env_span v,const char*s){size_t n=strlen(s);return n<=v.n&&!memcmp(v.p+v.n-n,s,n);}
static int env_read_u32(const unsigned char*b,size_t n,size_t*at,uint32_t*out){if(*at>n||n-*at<4)return 0;*out=rd32(b+*at);*at+=4;return 1;}
static int env_read_i64(const unsigned char*b,size_t n,size_t*at,int64_t*out){if(*at>n||n-*at<8)return 0;*out=(int64_t)rd64(b+*at);*at+=8;return 1;}
static int env_read_text(const unsigned char*b,size_t n,size_t*at,size_t cap,env_span*out){uint32_t m;if(!env_read_u32(b,n,at,&m)||m>cap||*at>n||m>n-*at)return 0;out->p=b+*at;out->n=m;*at+=m;return out->n==0|| (canonical_utf8_identity(out->p,out->n)&&!env_has_control(*out));}
static int env_identifier(env_span v){return v.n>0&&v.n<=128&&!env_has_byte(v,'/')&&!env_has_byte(v,'\\')&&!env_has_byte(v,':')&&!env_has_byte(v,' ');}
static int env_abs_path(env_span v){return v.n>0&&v.n<=4096&&!env_has_byte(v,'\\')&&!env_contains(v,"/../")&&!env_contains(v,"//")&&!(v.n>=3&&v.p[v.n-3]=='/'&&v.p[v.n-2]=='.'&&v.p[v.n-1]=='.')&&(v.p[0]=='/'||(v.n>=3&&v.p[1]==':'&&v.p[2]=='/'));}
static int env_sha256(env_span v){if(v.n!=71||memcmp(v.p,"sha256:",7))return 0;for(size_t i=7;i<v.n;i++)if(!((v.p[i]>='0'&&v.p[i]<='9')||(v.p[i]>='a'&&v.p[i]<='f')))return 0;return 1;}
static int env_plan_body(const unsigned char*b,size_t n){
    size_t at=0;uint32_t count,kind,argc;int64_t total,processes,timeout,out,err;env_span plan,root,resource,arg;env_tool tools[64];env_probe probes[64];
    if(!env_read_u32(b,n,&at,&count)||count!=1||!env_read_text(b,n,&at,128,&plan)||!env_read_text(b,n,&at,4096,&root)||plan.n==0||env_blank(plan)||!env_abs_path(root)||root.n==1||root.p[root.n-1]=='/'||!env_read_i64(b,n,&at,&total)||!env_read_i64(b,n,&at,&processes)||total<=0||total>67108864||processes<0||processes>64||!env_read_u32(b,n,&at,&count)||count>64)return 0;
    for(uint32_t i=0;i<count;i++){if(!env_read_text(b,n,&at,128,&tools[i].id)||!env_read_text(b,n,&at,4096,&tools[i].path)||!env_read_text(b,n,&at,128,&tools[i].hash)||!env_identifier(tools[i].id)||!env_abs_path(tools[i].path)||!env_sha256(tools[i].hash))return 0;for(uint32_t j=0;j<i;j++)if(env_span_eq(tools[i].id,tools[j].id))return 0;}uint32_t tool_count=count;
    if(!env_read_u32(b,n,&at,&count)||count>64)return 0;
    for(uint32_t i=0;i<count;i++){if(!env_read_text(b,n,&at,128,&probes[i].id)||!env_read_text(b,n,&at,128,&probes[i].schema)||!env_read_i64(b,n,&at,&probes[i].args)||!env_read_i64(b,n,&at,&probes[i].timeout)||!env_read_i64(b,n,&at,&probes[i].out)||!env_read_i64(b,n,&at,&probes[i].err)||!env_identifier(probes[i].id)||!env_identifier(probes[i].schema)||probes[i].args<0||probes[i].args>64||probes[i].timeout<=0||probes[i].timeout>600000||probes[i].out<0||probes[i].out>16777216||probes[i].err<0||probes[i].err>16777216)return 0;for(uint32_t j=0;j<i;j++)if(env_span_eq(probes[i].id,probes[j].id))return 0;}uint32_t probe_count=count;
    if(!env_read_u32(b,n,&at,&count)||count>1024)return 0;int64_t used=0,spawned=0;
    for(uint32_t i=0;i<count;i++){if(!env_read_u32(b,n,&at,&kind)||kind<1||kind>24||!env_read_text(b,n,&at,4096,&resource)||!env_read_u32(b,n,&at,&argc)||argc>64)return 0;size_t arg_bytes=0;for(uint32_t j=0;j<argc;j++){if(!env_read_text(b,n,&at,1024,&arg)||arg_bytes>4096-arg.n)return 0;arg_bytes+=arg.n;}if(!env_read_i64(b,n,&at,&timeout)||!env_read_i64(b,n,&at,&out)||!env_read_i64(b,n,&at,&err)||timeout<=0||timeout>600000||out<0||out>16777216||err<0||err>16777216||out>total-used)return 0;used+=out;if(err>total-used)return 0;used+=err;
        if((resource.n==0&&kind!=2)||resource.n>4096||((kind!=2)&&env_blank(resource)))return 0;if(kind==2&&(resource.n!=0||argc!=0))return 0;if(kind==3&&(argc!=0||resource.n==0||resource.p[0]=='/'||env_has_byte(resource,'\\')||env_has_byte(resource,':')||env_span_eq(resource,(env_span){(const unsigned char*)"..",2})||env_starts(resource,"../")||env_contains(resource,"/../")||env_ends(resource,"/..")))return 0;if((kind==1||(kind>=5&&kind<=23))&&(!env_identifier(resource)))return 0;
        if(kind==4){int found=0;for(uint32_t j=0;j<tool_count;j++)if(env_span_eq(resource,tools[j].id))found=1;if(!found)return 0;spawned++;}
        if(kind>=5&&kind<=23){int found=0;for(uint32_t j=0;j<probe_count;j++)if(env_span_eq(resource,probes[j].id)){if(argc>probes[j].args||timeout>probes[j].timeout||out>probes[j].out||err>probes[j].err)return 0;found=1;}if(!found)return 0;}
    }return spawned<=processes&&at==n;
}
static int tuple_one_bytes_events(const unsigned char*p,size_t n,size_t payload){
    return n==96&&rd64(p)==1&&rd64(p+8)>>32==2&&rd64(p+16)==3&&rd64(p+24)==1&&
        rd64(p+32)==23&&rd64(p+40)==payload&&rd64(p+48)==24&&rd64(p+56)==0&&
        rd64(p+64)==4&&rd64(p+72)==0&&rd64(p+80)==2&&rd64(p+88)==0;
}
static int tuple_one_text_events(const unsigned char*p,size_t n,size_t payload){
    return n==96&&rd64(p)==1&&rd64(p+8)>>32==2&&rd64(p+16)==3&&rd64(p+24)==1&&
        rd64(p+32)==25&&rd64(p+40)==payload&&rd64(p+48)==26&&rd64(p+56)==0&&
        rd64(p+64)==4&&rd64(p+72)==0&&rd64(p+80)==2&&rd64(p+88)==0;
}
static int registered_operation_matches(const unsigned char*p,size_t n){
    size_t m=registered_operation?strlen(registered_operation):0;
    return m>0&&m<=4096&&n==m&&!memcmp(p,registered_operation,m);
}
static int emit_result(const unsigned char *req,const size_t bs[5],const size_t dl[5],
    const unsigned char *payload,size_t payload_len,uint64_t tag,uint64_t width){
    size_t o=0;
    if(!append(&o,"RTHIOV2\0",8)||!append64(&o,2)||!append64(&o,rd64(req+8))||!append64(&o,rd64(req+16))||!append64(&o,0)||!append64(&o,rd64(req+24))||!append64(&o,0)||!append64(&o,1)||!append64(&o,0))return 76;
    for(unsigned b=0;b<5;b++){for(unsigned q=0;q<6;q++)if(!append64(&o,rd64(req+bs[b]+q*8)))return 76;if(!append64(&o,1))return 76;}
    for(unsigned b=0;b<5;b++)if(!append(&o,req+bs[b]+IO_TYPE_FIXED,dl[b]))return 76;
    if(!append64(&o,6)||!append64(&o,tag==20?3:4)||!append64(&o,payload_len)||
       !append64(&o,1)||!append64(&o,3ULL<<32)||!append64(&o,tag)||!append64(&o,width))return 76;
    if((tag!=20&&!append64(&o,tag+1))||!append64(&o,2)||!append64(&o,0)||!append(&o,payload,payload_len))return 76;
    if(!unit_stream(&o,4)||!unit_stream(&o,5))return 76;
    if(printf("RTHAL2 %zu\n",o)<0||!writehex(io_out,o))return 77;return 0;
}
/* Adapter 4 is the explicitly idempotent V3 EnvAccess `record` executor.
 * Its result is a fresh canonical receipt constructed after strict plan
 * validation; it never receives a Pure output/error/result seed. */
static int emit_effect_result(const unsigned char *req,const size_t bs[5],const size_t dl[5],
    const unsigned char *payload,size_t payload_len){
    size_t o=0;
    if(!append(&o,"RTHIOV2\0",8)||!append64(&o,2)||!append64(&o,rd64(req+8))||!append64(&o,rd64(req+16))||!append64(&o,0)||!append64(&o,rd64(req+24))||!append64(&o,0)||!append64(&o,1)||!append64(&o,0))return 76;
    for(unsigned b=0;b<5;b++){for(unsigned q=0;q<6;q++)if(!append64(&o,rd64(req+bs[b]+q*8)))return 76;if(!append64(&o,1))return 76;}
    for(unsigned b=0;b<5;b++)if(!append(&o,req+bs[b]+IO_TYPE_FIXED,dl[b]))return 76;
    if(!unit_stream(&o,3)||!unit_stream(&o,4)||!append64(&o,6)||!append64(&o,4)||!append64(&o,payload_len)||
       !append64(&o,1)||!append64(&o,5ULL<<32)||!append64(&o,23)||!append64(&o,payload_len)||
       !append64(&o,24)||!append64(&o,0)||!append64(&o,2)||!append64(&o,0)||!append(&o,payload,payload_len))return 76;
    if(printf("RTHAL2 %zu\n",o)<0||!writehex(io_out,o))return 77;return 0;
}
static int run_registered_operation(const unsigned char *req,const size_t bs[5],const size_t dl[5],
    size_t op,size_t input,size_t inn,size_t op_ev,size_t ope,size_t opn,size_t in_ev,size_t ine){
    const unsigned char *param=req+input;const unsigned char *events=req+in_ev;
    const unsigned char *input_desc=req+bs[1]+IO_TYPE_FIXED;
    const unsigned char *meta=req+bs[4]+IO_TYPE_FIXED+dl[4];
    if(!descriptor_is(req+bs[0]+IO_TYPE_FIXED,dl[0],"v2;text:utf8")||
       !text_events(req+op_ev,ope,opn,1)||!canonical_utf8_identity(req+op,opn)||
       !transcript_ok(events,ine/16,2)||rd32(meta)!=0||rd32(meta+4)!=6||
       rd32(meta+8)!=0||rd32(meta+20)!=6||rd32(meta+24)!=1||
       rd32(meta+36)!=6||rd32(meta+40)!=6||rd32(meta+44)!=6)return 74;
    /* Each entry names one exact compiler operation identity; there is no
       prefix, suffix, descriptor-only, or "copy the Pure exit" fallback. */
    if(!registered_operation_matches(req+op,opn))return provider_unknown();
    if(registered_adapter==1&&descriptor_is(input_desc,dl[1],"v2;tuple;1;8:v2;bytes")&&descriptor_is(req+bs[2]+IO_TYPE_FIXED,dl[2],"v2;bytes")&&
       tuple_one_bytes_events(events,ine,inn)&&unit_descriptor(req+bs[3]+IO_TYPE_FIXED,dl[3])&&unit_descriptor(req+bs[4]+IO_TYPE_FIXED,dl[4]))
        return emit_result(req,bs,dl,param,inn,23,inn);
    if(registered_adapter==2&&descriptor_is(input_desc,dl[1],"v2;tuple;1;8:v2;bytes")&&descriptor_is(req+bs[2]+IO_TYPE_FIXED,dl[2],"v2;u64")&&
       tuple_one_bytes_events(events,ine,inn)&&unit_descriptor(req+bs[3]+IO_TYPE_FIXED,dl[3])&&unit_descriptor(req+bs[4]+IO_TYPE_FIXED,dl[4])){
        uint64_t x=0;for(size_t i=0;i<inn;i++)x^=(uint64_t)param[i]<<(8*(i&7));wr64(io_eff,x);return emit_result(req,bs,dl,io_eff,8,20,8);
    }
    if(registered_adapter==3&&descriptor_is(input_desc,dl[1],"v2;tuple;1;12:v2;text:utf8")&&descriptor_is(req+bs[2]+IO_TYPE_FIXED,dl[2],"v2;text:utf8")&&
       tuple_one_text_events(events,ine,inn)&&canonical_utf8_identity(param,inn)&&unit_descriptor(req+bs[3]+IO_TYPE_FIXED,dl[3])&&unit_descriptor(req+bs[4]+IO_TYPE_FIXED,dl[4])){
        /* Reverse only ASCII code units; non-ASCII is deliberately unsupported
           until a bounded code-point adapter is registered. */
        for(size_t i=0;i<inn;i++)if(param[i]&0x80)return provider_unknown();
        for(size_t i=0;i<inn;i++)io_eff[i]=param[inn-1-i];return emit_result(req,bs,dl,io_eff,inn,25,inn);
    }
    return provider_unknown();
}
static int run_registered_effect(const unsigned char *req,const size_t bs[5],const size_t dl[5],
    size_t op,size_t op_ev,size_t ope,size_t opn,const unsigned char *effect,size_t effect_len){
    const unsigned char *meta=req+bs[4]+IO_TYPE_FIXED+dl[4];
    if(registered_adapter!=4||!registered_operation_matches(req+op,opn)||
       !descriptor_is(req+bs[0]+IO_TYPE_FIXED,dl[0],"v2;text:utf8")||!text_events(req+op_ev,ope,opn,1)||
       !canonical_utf8_identity(req+op,opn)||!unit_descriptor(req+bs[2]+IO_TYPE_FIXED,dl[2])||
       !unit_descriptor(req+bs[3]+IO_TYPE_FIXED,dl[3])||!descriptor_is(req+bs[4]+IO_TYPE_FIXED,dl[4],"v2;bytes")||
       rd32(meta)!=1||rd32(meta+4)!=6||rd32(meta+8)!=0||rd32(meta+20)!=6||rd32(meta+24)!=1||
       rd32(meta+36)!=6||rd32(meta+40)!=6||rd32(meta+44)!=6||effect_len<8)return provider_unknown();
    uint32_t payload=rd32(effect),events=rd32(effect+4);
    if(payload>IO_CAP||events!=64||payload>effect_len-8||events!=effect_len-8-payload||
       !bytes_events(effect+8+payload,events,payload,5)||payload<21||memcmp(effect+8,"RTHALENV3",9)||
       rd32(effect+17)!=3||rd32(effect+21)!=1||rd32(effect+25)!=payload-21||
       !env_plan_body(effect+29,payload-21)||!execute_idempotent_record(req))return provider_unknown();
    emit_effect_result(req,bs,dl,effect+8,payload);
}
static int run_io(int replay){
    char line[96];unsigned long long rn,en;int used=0;
    if(!fgets(line,sizeof line,stdin)||!strchr(line,'\n')||sscanf(line,"RTHAL2 %llu %llu%n",&rn,&en,&used)!=2||line[used]!='\n'||line[used+1])return 70;
    if(!rn||rn>IO_CAP||en>IO_CAP||rn>SIZE_MAX/2||en>SIZE_MAX/2||(!replay&&en)|| (replay&&en<8))return 71;
    /* The pinned host keeps the descriptor open; declared lengths are the
       frame boundary and the child must not wait for EOF. */
    size_t r=(size_t)rn,e=(size_t)en;if(!readhex(io_req,r)||!readhex(io_eff,e))return 72;
    if(r<IO_HEADER||rd32(io_req)!=UINT32_C(0x324f4948)||io_req[4]!=2||
       io_req[5]||io_req[6]||io_req[7])return 73;
    size_t at=IO_HEADER,bs[5],dl[5];
    for(unsigned b=0;b<5;b++){bs[b]=at;if(!grow(&at,IO_TYPE_FIXED,r))return 73;uint64_t a=rd64(io_req+bs[b]+40);uint32_t n=rd32(io_req+bs[b]+52);if(io_req[bs[b]+48]!=1||io_req[bs[b]+49]||io_req[bs[b]+50]||io_req[bs[b]+51]||a!=n||!n||!grow(&at,n,r))return 73;dl[b]=n;}
    size_t meta=at;if(!grow(&at,48,r))return 73;const unsigned char*m=io_req+meta;
    uint32_t opn=rd32(m+12),ope=rd32(m+16),inn=rd32(m+28),ine=rd32(m+32);
    uint32_t op_kind=rd32(m);
    if(op_kind>1||op_kind!=(uint32_t)replay||ope%16||ine%16)return 74;
    size_t op=at;if(!grow(&at,opn,r))return 73;size_t op_ev=at;if(!grow(&at,ope,r))return 73;size_t in=at;if(!grow(&at,inn,r))return 73;size_t in_ev=at;if(!grow(&at,ine,r)||at!=r)return 73;
    if(!transcript_ok(io_req+op_ev,ope/16,1)||!transcript_ok(io_req+in_ev,ine/16,2))return 74;
    /* V3 typed execution is compare-only until a native effect adapter is
       registered.  It receives only operation and parameter request fields. */
    if(registered_operation){
        if(replay)return run_registered_effect(io_req,bs,dl,op,op_ev,ope,opn,io_eff,e);
        return run_registered_operation(io_req,bs,dl,op,in,inn,op_ev,ope,opn,in_ev,ine);
    }
    if(rd32(m+4)!=6||rd32(m+8)!=0||rd32(m+20)!=6||rd32(m+24)!=1||rd32(m+36)!=6||rd32(m+40)!=6||rd32(m+44)!=6)return 74;
    if(dl[1]!=dl[2]||memcmp(io_req+bs[1],io_req+bs[2],48)||memcmp(io_req+bs[1]+IO_TYPE_FIXED,io_req+bs[2]+IO_TYPE_FIXED,dl[1])||
       !unit_descriptor(io_req+bs[3]+IO_TYPE_FIXED,dl[3])||
       (!replay&&!unit_descriptor(io_req+bs[4]+IO_TYPE_FIXED,dl[4])))return 74;
    size_t ep=0,ee=0,epa=8,eea=0;if(replay){ep=rd32(io_eff);ee=rd32(io_eff+4);eea=8+ep;if(ep>e-8||ee>e-8-ep||eea+ee!=e||ee%16||!transcript_ok(io_eff+eea,ee/16,5))return 75;}
    size_t o=0;if(!append(&o,"RTHIOV2\0",8)||!append64(&o,2)||!append64(&o,rd64(io_req+8))||!append64(&o,rd64(io_req+16))||!append64(&o,0)||!append64(&o,rd64(io_req+24))||!append64(&o,0)||!append64(&o,1)||!append64(&o,0))return 76;
    for(unsigned b=0;b<5;b++){for(unsigned q=0;q<6;q++)if(!append64(&o,rd64(io_req+bs[b]+q*8)))return 76;if(!append64(&o,1))return 76;}
    for(unsigned b=0;b<5;b++)if(!append(&o,io_req+bs[b]+IO_TYPE_FIXED,dl[b]))return 76;
    if(!append64(&o,6)||!append64(&o,ine/16)||!append64(&o,inn))return 76;
    size_t copied=o;if(!append(&o,io_req+in_ev,ine))return 76;wr64(io_out+copied+8,(rd64(io_out+copied+8)&UINT64_C(0xffffffff))|(UINT64_C(3)<<32));if(!append(&o,io_req+in,inn))return 76;
    if(!unit_stream(&o,4))return 76;
    if(replay){if(!append64(&o,6)||!append64(&o,ee/16)||!append64(&o,ep)||!append(&o,io_eff+eea,ee)||!append(&o,io_eff+epa,ep))return 76;}else if(!unit_stream(&o,5))return 76;
    if(printf("RTHAL2 %zu\n",o)<0||!writehex(io_out,o))return 77;return 0;
}

static const uint64_t GOLDEN = UINT64_C(0x9e3779b97f4a7c15);
static const uint64_t FNV_PRIME = UINT64_C(0x00000100000001b3);
static const uint64_t EFFECT_DOMAIN = UINT64_C(0xd1b54a32d192ed03);
static const uint64_t TRACE_DOMAIN = UINT64_C(0x94d049bb133111eb);

static int valid_i64(const char *value) {
    char *end = NULL;
    if (value == NULL || value[0] == '\0') return 0;
    size_t index = value[0] == '-' ? 1U : 0U;
    if (value[index] == '\0') return 0;
    for (; value[index] != '\0'; ++index) {
        if (value[index] < '0' || value[index] > '9') return 0;
    }
    errno = 0;
    (void)strtoll(value, &end, 10);
    return errno == 0 && end != value && *end == '\0';
}

static uint64_t parse_word(const char *value) {
    return (uint64_t)strtoll(value, NULL, 10);
}

static uint64_t rotl64(uint64_t value, unsigned shift) {
    shift &= 63U;
    return (value << shift) | (value >> ((64U - shift) & 63U));
}

static uint64_t mix64(uint64_t value) {
    value ^= value >> 30U;
    value *= UINT64_C(0xbf58476d1ce4e5b9);
    value ^= value >> 27U;
    value *= UINT64_C(0x94d049bb133111eb);
    return value ^ (value >> 31U);
}

static int print_word(uint64_t word) {
    if ((word & (UINT64_C(1) << 63U)) == 0)
        return printf(" %" PRIu64, word) >= 0;
    return printf(" -%" PRIu64, (~word) + UINT64_C(1)) >= 0;
}

static int install_registered_operation(const char *id,const char *adapter){
    char *end=NULL;unsigned long value;
    if(!id||!adapter||!canonical_utf8_identity((const unsigned char*)id,strlen(id))||strlen(id)>4096)return 0;
    errno=0;value=strtoul(adapter,&end,10);
    if(errno||end==adapter||*end||value<1||value>4)return 0;
    registered_operation=id;registered_adapter=(unsigned)value;return 1;
}

int main(int argc, char **argv) {
    if(argc==3&&strcmp(argv[1],"rthal-io-v2")==0){if(strcmp(argv[2],"compare")==0)return run_io(0);if(strcmp(argv[2],"replay")==0)return run_io(1);return 66;}
    if(argc==5&&strcmp(argv[1],"rthal-io-v3")==0&&install_registered_operation(argv[3],argv[4])){
        if(strcmp(argv[2],"compare")==0){if(registered_adapter==4)return 64;return run_io(0);}
        if(strcmp(argv[2],"replay")==0){if(registered_adapter!=4)return 64;return run_io(1);}
        return 66;
    }
    if (argc != QUERY_ARGC && argc != REPLAY_ARGC) return 64;
    if (strcmp(argv[1], "rthal-scalar-v2") != 0) return 65;
    if (strcmp(argv[2], "compare") != 0 && strcmp(argv[2], "replay") != 0) return 66;
    if (strcmp(argv[4], "0") != 0 && strcmp(argv[4], "1") != 0) return 67;
    for (int index = 3; index < argc; ++index) {
        if (!valid_i64(argv[index])) return 68;
    }
    const int effect = argv[4][0] == '1';
    if ((!effect && strcmp(argv[2], "compare") != 0) ||
        (effect && strcmp(argv[2], "replay") != 0)) return 67;
    if ((!effect && argc != QUERY_ARGC) || (effect && argc != REPLAY_ARGC)) return 64;
    uint64_t operation[4], input[4], replay_trace[4];
    uint64_t outcome[4], trace[4];
    for (unsigned i = 0; i < 4U; ++i) {
        operation[i] = parse_word(argv[5 + i]);
        input[i] = parse_word(argv[9 + i]);
        replay_trace[i] = effect ? parse_word(argv[13 + i]) : 0;
    }
    for (unsigned i = 0; i < 4U; ++i) {
        uint64_t base = operation[i] ^ rotl64(input[(i + 1U) & 3U], 7U + 11U * i)
            ^ (GOLDEN + FNV_PRIME * i);
        if (effect)
            base ^= rotl64(replay_trace[(i + 2U) & 3U], 13U + 7U * i)
                ^ EFFECT_DOMAIN;
        outcome[i] = mix64(base);
        trace[i] = effect ? replay_trace[i] : mix64(base ^ TRACE_DOMAIN);
    }
    if (printf("RTHAL1") < 0) return 69;
    for (unsigned i = 0; i < 4U; ++i) if (!print_word(outcome[i])) return 69;
    for (unsigned i = 0; i < 4U; ++i) if (!print_word(0)) return 69;
    for (unsigned i = 0; i < 4U; ++i) if (!print_word(trace[i])) return 69;
    if (printf("\n") < 0) return 69;
    return 0;
}
