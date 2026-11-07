/* Include only inside runtime_native.c, after its registered value helpers.
 * No Rust RuntimeValue or collection layout enters this translation unit. */
#include "runtime_process_interactive_v1_abi.h"

static SplArray* oiv1_native_words(uint64_t count) {
    SplArray* value=rt_array_new_with_cap_u64((int64_t)count);
    RtCoreArray* array=rt_core_as_array((int64_t)(uintptr_t)value);
    if (!array || (uint64_t)array->cap<count) { if (value) rt_array_free(value); return NULL; }
    memset(array->data,0,(size_t)count*8); array->len=(int64_t)count; return value;
}
static void oiv1_native_store(SplArray* value,const void* words,uint64_t count) {
    RtCoreArray* array=rt_core_as_array((int64_t)(uintptr_t)value);
    memcpy(array->data,words,(size_t)count*8);
}
static Oiv1Deadline oiv1_native_deadline(int64_t clock,int64_t expires) {
    Oiv1Deadline result={1,sizeof(Oiv1Deadline),(uint64_t)clock,expires}; return result;
}
static void oiv1_native_bad(Oiv1Receipt* receipt) {
    memset(receipt,0,sizeof(*receipt)); receipt->version=1; receipt->size=sizeof(*receipt);
    receipt->status=OIV1_STATUS_INVALIDARGUMENT; receipt->error_domain=OIV1_ERROR_CONTRACT;
    receipt->validity_mask=OIV1_VALID_ERROR;
}
static int64_t oiv1_native_resolve(const Oiv1Receipt* receipt,uint64_t action) {
    if (!(receipt->flags&OIV1_FLAG_LOANPRESENT)) return OIV1_RESOLVE_RECORDED;
    Oiv1ResolveRequest request={1,sizeof(request),
        {receipt->ticket0,receipt->ticket1,receipt->ticket2,receipt->ticket3},action};
    return simple_owned_interactive_v1_resolve(&request,sizeof(request));
}
static void oiv1_native_receipt(SplArray* value,const Oiv1Receipt* source) {
    Oiv1Receipt receipt=*source;
    receipt.flags&=~(OIV1_FLAG_LOANPRESENT|OIV1_FLAG_STARTPUBLICATIONPENDING|OIV1_FLAG_OUTPUTDELIVERYRESERVED);
    receipt.ticket0=receipt.ticket1=receipt.ticket2=receipt.ticket3=0;
    oiv1_native_store(value,&receipt,32);
}

SplArray* rt_process_owned_interactive_v1_capabilities_value(void) {
    SplArray* value=oiv1_native_words(16); if (!value) return NULL;
    Oiv1Capabilities caps;
    if (simple_owned_interactive_v1_capabilities(&caps,sizeof(caps))!=0) { rt_array_free(value); return NULL; }
    oiv1_native_store(value,&caps,16); return value;
}
SplArray* rt_process_owned_interactive_v1_deadline_value(int64_t timeout_ms) {
    SplArray* value=oiv1_native_words(8); if (!value) return NULL;
    Oiv1DeadlineRequest request={1,sizeof(request),(uint64_t)timeout_ms};
    Oiv1Deadline deadline; Oiv1Receipt receipt;
    if (simple_owned_interactive_v1_deadline(&request,sizeof(request),&deadline,&receipt,sizeof(receipt))!=0) {
        rt_array_free(value); return NULL;
    }
    uint64_t words[8]={1,sizeof(deadline),deadline.clock_tag,(uint64_t)deadline.expires_ms,
        receipt.status,receipt.error_domain,receipt.error_code,0};
    oiv1_native_store(value,words,8); return value;
}
SplArray* rt_process_owned_interactive_v1_start_value(const uint8_t* command,uint64_t command_len,SplArray* args,
        int64_t clock,int64_t expires,int64_t input_cap,int64_t output_cap,int64_t error_cap) {
    /* Allocate the final returned object BEFORE creating even a reserved owner. */
    SplArray* value=oiv1_native_words(32); if (!value) return NULL;
    Oiv1Receipt receipt; oiv1_native_bad(&receipt);
    RtCoreArray* arguments=rt_core_as_array((int64_t)(uintptr_t)args);
    Oiv1ConstSpan spans[128]; memset(spans,0,sizeof(spans));
    if (!arguments || (arguments->flags&(RT_CORE_ARRAY_FLAG_BYTES|RT_CORE_ARRAY_FLAG_U64_PACKED)) ||
        arguments->len<0 || arguments->len>128) goto done;
    for (int64_t i=0;i<arguments->len;i++) {
        RtCoreString* text=rt_core_as_string(((int64_t*)arguments->data)[i]);
        if (!text) goto done; spans[i].data=(const uint8_t*)text->data; spans[i].len=text->len;
    }
    Oiv1StartRequest request={1,sizeof(request),{command,command_len},{spans,(uint64_t)arguments->len},
        oiv1_native_deadline(clock,expires),(uint64_t)input_cap,(uint64_t)output_cap,(uint64_t)error_cap,0};
    if (simple_owned_interactive_v1_start_begin(&request,sizeof(request),&receipt,sizeof(receipt))!=0) goto done;
    /* Packed integer words never box/allocate during projection. */
    oiv1_native_receipt(value,&receipt);
    int64_t resolution=oiv1_native_resolve(&receipt,1);
    if (resolution!=OIV1_RESOLVE_RECORDED && resolution!=OIV1_RESOLVE_ALREADYSAME) {
        /* An internal bridge invariant failure is not successful startup.
         * ABORT only succeeds while unresolved; a contradictory actor cannot
         * be allowed to manufacture native authority through this boundary. */
        (void)oiv1_native_resolve(&receipt,2);
        /* Preserve the already materialized owner receipt even on a bridge
         * invariant failure. The safe caller can cancel/collect; NULL would
         * throw away its only possible lease. Normal valid tickets are
         * guaranteed Recorded/AlreadySame by the permanent-slot CAS. */
        receipt.status=OIV1_STATUS_PROJECTIONFAILURE; receipt.flags|=OIV1_FLAG_MAINTENANCEDEFERRED;
        oiv1_native_receipt(value,&receipt); return value;
    }
    return value;
done:
    oiv1_native_receipt(value,&receipt); return value;
}
SplArray* rt_process_owned_interactive_v1_write_some_value(int64_t handle,SplArray* bytes,int64_t offset,
        int64_t maximum,int64_t expected,int64_t clock,int64_t expires) {
    SplArray* value=oiv1_native_words(32); if (!value) return NULL;
    Oiv1Receipt receipt; oiv1_native_bad(&receipt);
    RtCoreArray* array=rt_core_as_array((int64_t)(uintptr_t)bytes);
    uint8_t copy[4096];
    if (!array || offset<0 || offset>array->len || maximum<0 || maximum>4096 || expected<0) goto done;
    uint64_t count=(uint64_t)(array->len-offset); if (count>(uint64_t)maximum) count=(uint64_t)maximum;
    for (uint64_t i=0;i<count;i++) {
        if (array->flags&RT_CORE_ARRAY_FLAG_BYTES) copy[i]=((uint8_t*)array->data)[offset+(int64_t)i];
        else {
            int64_t item=rt_array_get(bytes,offset+(int64_t)i);
            if (!rt_value_is_int(item)) goto done;
            int64_t integer=rt_value_as_int_wide(item); if (integer<0 || integer>255) goto done;
            copy[i]=(uint8_t)integer;
        }
    }
    Oiv1WriteRequest request={1,sizeof(request),handle,{copy,count},0,count,(uint64_t)expected,oiv1_native_deadline(clock,expires)};
    (void)simple_owned_interactive_v1_write_some(&request,sizeof(request),&receipt,sizeof(receipt));
done:
    oiv1_native_receipt(value,&receipt); return value;
}
int64_t* rt_process_owned_interactive_v1_poll_value(int64_t handle,int64_t clock,int64_t expires,
        int64_t wait_ms,int64_t output_max,int64_t error_max) {
    /* Tuple, both byte arrays and all receipt words exist before any reservation. */
    int valid=output_max>=0 && output_max<=65536 && error_max>=0 && error_max<=65536 && wait_ms>=0 && wait_ms<=250;
    if (!valid) output_max=error_max=0;
    SplArray* words=oiv1_native_words(32);
    SplArray* output=rt_byte_array_new_len((uint64_t)output_max);
    SplArray* error=rt_byte_array_new_len((uint64_t)error_max);
    int64_t tuple=rt_tuple_new(3);
    if (!words || !output || !error || !tuple) {
        if (words) rt_array_free(words); if (output) rt_array_free(output); if (error) rt_array_free(error);
        if (tuple) rt_array_free((SplArray*)(uintptr_t)tuple); return NULL;
    }
    if (!rt_tuple_set(tuple,0,(int64_t)(uintptr_t)output) || !rt_tuple_set(tuple,1,(int64_t)(uintptr_t)error) ||
        !rt_tuple_set(tuple,2,(int64_t)(uintptr_t)words)) {
        rt_array_free(words); rt_array_free(output); rt_array_free(error); rt_array_free((SplArray*)(uintptr_t)tuple); return NULL;
    }
    RtCoreArray* out_array=rt_core_as_array((int64_t)(uintptr_t)output);
    RtCoreArray* err_array=rt_core_as_array((int64_t)(uintptr_t)error);
    Oiv1PollRequest request={1,sizeof(request),handle,oiv1_native_deadline(clock,expires),(uint64_t)wait_ms,
        {(uint8_t*)out_array->data,(uint64_t)output_max},{(uint8_t*)err_array->data,(uint64_t)error_max}};
    Oiv1Receipt receipt;
    if (valid) (void)simple_owned_interactive_v1_poll_begin(&request,sizeof(request),&receipt,sizeof(receipt));
    else oiv1_native_bad(&receipt);
    out_array->len=(int64_t)receipt.stdout_count; err_array->len=(int64_t)receipt.stderr_count;
    oiv1_native_receipt(words,&receipt);
    int64_t resolution=oiv1_native_resolve(&receipt,1);
    if (resolution!=OIV1_RESOLVE_RECORDED && resolution!=OIV1_RESOLVE_ALREADYSAME) {
        (void)oiv1_native_resolve(&receipt,2);
        receipt.stdout_delivered_total-=receipt.stdout_count; receipt.stderr_delivered_total-=receipt.stderr_count;
        receipt.stdout_count=receipt.stderr_count=0; receipt.validity_mask&=~OIV1_VALID_OUTPUT;
        receipt.status=OIV1_STATUS_PROJECTIONFAILURE; receipt.flags|=OIV1_FLAG_MAINTENANCEDEFERRED;
        out_array->len=err_array->len=0; oiv1_native_receipt(words,&receipt);
        return (int64_t*)(uintptr_t)tuple;
    }
    return (int64_t*)(uintptr_t)tuple;
}
static SplArray* oiv1_native_control(int64_t handle,int64_t clock,int64_t expires,int discard,int operation) {
    SplArray* value=oiv1_native_words(32); if (!value) return NULL;
    Oiv1ControlRequest request={1,sizeof(request),handle,oiv1_native_deadline(clock,expires),(uint64_t)discard};
    Oiv1Receipt receipt;
    if (operation==1) (void)simple_owned_interactive_v1_close_stdin(&request,sizeof(request),&receipt,sizeof(receipt));
    else if (operation==2) (void)simple_owned_interactive_v1_cancel(&request,sizeof(request),&receipt,sizeof(receipt));
    else (void)simple_owned_interactive_v1_collect(&request,sizeof(request),&receipt,sizeof(receipt));
    oiv1_native_receipt(value,&receipt); return value;
}
SplArray* rt_process_owned_interactive_v1_close_stdin_value(int64_t h,int64_t c,int64_t e) { return oiv1_native_control(h,c,e,0,1); }
SplArray* rt_process_owned_interactive_v1_cancel_value(int64_t h,int64_t c,int64_t e) { return oiv1_native_control(h,c,e,0,2); }
SplArray* rt_process_owned_interactive_v1_collect_value(int64_t h,int64_t c,int64_t e,bool d) { return oiv1_native_control(h,c,e,d,3); }
SplArray* rt_process_owned_interactive_v1_release_value(int64_t handle) {
    SplArray* value=oiv1_native_words(32); if (!value) return NULL;
    Oiv1ReleaseRequest request={1,sizeof(request),handle}; Oiv1Receipt receipt;
    (void)simple_owned_interactive_v1_release(&request,sizeof(request),&receipt,sizeof(receipt));
    oiv1_native_receipt(value,&receipt); return value;
}
