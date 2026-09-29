/* Frozen independent C oracle copied before the pure-Simple migration. */
#include "cosmos_nvme_admin_policy_oracle.h"

#define O_CONTINUE 0xFFFFFFFFU
#define O_MAX_QUEUES 4U
#define O_MAX_ENTRIES 64U
#define O_NSID 1U
#define O_NSID_ALL 0xFFFFFFFFU

static unsigned int o_status(unsigned int sct, unsigned int sc,
                             unsigned int dnr) {
    return (dnr << 16U) | (sct << 8U) | sc;
}

unsigned int cosmos_nvme_admin_oracle_status_success(void) {
    return o_status(0U, 0U, 0U);
}

unsigned int cosmos_nvme_admin_oracle_status_generic(unsigned int sc) {
    return o_status(0U, sc, 1U);
}

static unsigned int o_specific(unsigned int sc) {
    return o_status(1U, sc, 1U);
}

static unsigned int o_min(unsigned int left, unsigned int right) {
    return left < right ? left : right;
}

static int o_power_of_two(unsigned int value) {
    return value != 0U && (value & (value - 1U)) == 0U;
}

static unsigned int o_log2(unsigned int value) {
    unsigned int result = 0U;
    while (value > 1U) {
        value >>= 1U;
        result++;
    }
    return result;
}

static int o_no_payload(unsigned int low1, unsigned int high1,
                        unsigned int low2, unsigned int high2,
                        unsigned int bytes) {
    return low1 == 0U && high1 == 0U && low2 == 0U && high2 == 0U &&
        bytes == 0U;
}

static int o_queue_base(unsigned int low1, unsigned int high1,
                        unsigned int low2, unsigned int high2,
                        unsigned int bytes) {
    return bytes == 0U && low2 == 0U && high2 == 0U &&
        (low1 != 0U || high1 != 0U) && (low1 & 0xFFFU) == 0U &&
        high1 <= 0xFU;
}

static int o_opcode(unsigned int opcode) {
    switch (opcode) {
    case 0x00U: case 0x01U: case 0x02U: case 0x04U: case 0x05U:
    case 0x06U: case 0x08U: case 0x09U: case 0x0AU: case 0x0CU:
        return 1;
    default:
        return 0;
    }
}

static int o_payload(unsigned int low1, unsigned int high1,
                     unsigned int low2, unsigned int high2,
                     unsigned int payload_bytes, unsigned int required) {
    unsigned int first_room;
    int second;
    if (payload_bytes != required || (low1 == 0U && high1 == 0U) ||
        (low1 & 3U) != 0U) {
        return 0;
    }
    first_room = 4096U - (low1 & 0xFFFU);
    second = low2 != 0U || high2 != 0U;
    if (required <= first_room) {
        return !second;
    }
    return second && (low2 & 0xFFFU) == 0U;
}

static int o_queue_allowed(unsigned int negotiated, unsigned int queue_id) {
    return queue_id != 0U && queue_id <= negotiated &&
        queue_id <= O_MAX_QUEUES;
}

static int o_controller_nsid(unsigned int nsid) {
    return nsid == 0U || nsid == O_NSID;
}

static int o_smart_nsid(unsigned int nsid) {
    return nsid == O_NSID || nsid == O_NSID_ALL;
}

unsigned int cosmos_nvme_admin_oracle_identify_status(
    unsigned int nsid, unsigned int cdw10, unsigned int cdw11,
    unsigned int cdw12, unsigned int cdw13) {
    unsigned int cns = cdw10 & 0xFFU;
    if ((cdw10 & ~0xFFU) != 0U || cdw11 != 0U || cdw12 != 0U ||
        cdw13 != 0U) {
        return cosmos_nvme_admin_oracle_status_generic(0x02U);
    }
    if (cns == 1U) {
        return nsid == 0U ? cosmos_nvme_admin_oracle_status_success() :
            cosmos_nvme_admin_oracle_status_generic(0x0BU);
    }
    if (cns != 0U) {
        return cosmos_nvme_admin_oracle_status_generic(0x02U);
    }
    return nsid == O_NSID ? cosmos_nvme_admin_oracle_status_success() :
        cosmos_nvme_admin_oracle_status_generic(0x0BU);
}

unsigned int cosmos_nvme_admin_oracle_get_log_status(
    unsigned int nsid, unsigned int cdw10, unsigned int cdw11,
    unsigned int cdw12, unsigned int cdw13) {
    if (!o_smart_nsid(nsid)) {
        return cosmos_nvme_admin_oracle_status_generic(0x0BU);
    }
    if ((cdw10 & 0xFFU) != 0x02U) {
        return o_specific(0x09U);
    }
    if ((cdw10 & 0x00007F00U) != 0U ||
        ((cdw10 >> 16U) & 0xFFFFU) != 127U || cdw11 != 0U ||
        cdw12 != 0U || cdw13 != 0U) {
        return cosmos_nvme_admin_oracle_status_generic(0x02U);
    }
    return cosmos_nvme_admin_oracle_status_success();
}

unsigned int cosmos_nvme_admin_oracle_set_features_status(
    unsigned int nsid, unsigned int cdw10, unsigned int cdw11,
    unsigned int cdw12, unsigned int cdw13) {
    if (!o_controller_nsid(nsid)) {
        return cosmos_nvme_admin_oracle_status_generic(0x0BU);
    }
    if ((cdw10 & 0x7FFFFF00U) != 0U || cdw12 != 0U || cdw13 != 0U ||
        (cdw10 & 0xFFU) != 0x07U) {
        return cosmos_nvme_admin_oracle_status_generic(0x02U);
    }
    if ((cdw10 & 0x80000000U) != 0U) {
        return o_specific(0x0DU);
    }
    if ((cdw11 & 0xFFFFU) == 0xFFFFU || (cdw11 >> 16U) == 0xFFFFU) {
        return cosmos_nvme_admin_oracle_status_generic(0x02U);
    }
    return cosmos_nvme_admin_oracle_status_success();
}

unsigned int cosmos_nvme_admin_oracle_get_features_status(
    unsigned int nsid, unsigned int cdw10, unsigned int cdw11,
    unsigned int cdw12, unsigned int cdw13) {
    if (!o_controller_nsid(nsid)) {
        return cosmos_nvme_admin_oracle_status_generic(0x0BU);
    }
    if ((cdw10 & ~0x000007FFU) != 0U || (cdw10 & 0xFFU) != 0x07U ||
        ((cdw10 >> 8U) & 7U) != 0U || cdw11 != 0U || cdw12 != 0U ||
        cdw13 != 0U) {
        return cosmos_nvme_admin_oracle_status_generic(0x02U);
    }
    return cosmos_nvme_admin_oracle_status_success();
}

unsigned int cosmos_nvme_admin_oracle_create_cq_status(
    unsigned int negotiated, unsigned int existing, unsigned int nsid,
    unsigned int cdw10, unsigned int cdw11, unsigned int cdw12,
    unsigned int cdw13, unsigned int low1, unsigned int high1,
    unsigned int low2, unsigned int high2, unsigned int bytes) {
    unsigned int queue_id = cdw10 & 0xFFFFU;
    unsigned int entries = (cdw10 >> 16U) + 1U;
    if (nsid != 0U || cdw12 != 0U || cdw13 != 0U ||
        !o_queue_base(low1, high1, low2, high2, bytes)) {
        return cosmos_nvme_admin_oracle_status_generic(0x02U);
    }
    if (!o_queue_allowed(negotiated, queue_id)) return o_specific(0x01U);
    if (entries == 0U || entries > O_MAX_ENTRIES) return o_specific(0x02U);
    if ((cdw11 & 1U) == 0U || (cdw11 & 0x0000FFFCU) != 0U ||
        ((cdw11 & 2U) == 0U && (cdw11 >> 16U) != 0U)) {
        return cosmos_nvme_admin_oracle_status_generic(0x02U);
    }
    if ((cdw11 & 2U) != 0U && (cdw11 >> 16U) != 0U)
        return o_specific(0x08U);
    if (existing != 0U) return o_specific(0x01U);
    return cosmos_nvme_admin_oracle_status_success();
}

unsigned int cosmos_nvme_admin_oracle_create_sq_status(
    unsigned int negotiated, unsigned int completion_valid,
    unsigned int existing, unsigned int nsid, unsigned int cdw10,
    unsigned int cdw11, unsigned int cdw12, unsigned int cdw13,
    unsigned int low1, unsigned int high1, unsigned int low2,
    unsigned int high2, unsigned int bytes) {
    unsigned int queue_id = cdw10 & 0xFFFFU;
    unsigned int entries = (cdw10 >> 16U) + 1U;
    unsigned int cqid = cdw11 >> 16U;
    if (nsid != 0U || cdw12 != 0U || cdw13 != 0U ||
        (cdw11 & 1U) == 0U || (cdw11 & 0x0000FFF8U) != 0U ||
        !o_queue_base(low1, high1, low2, high2, bytes)) {
        return cosmos_nvme_admin_oracle_status_generic(0x02U);
    }
    if (!o_queue_allowed(negotiated, queue_id) ||
        !o_queue_allowed(negotiated, cqid)) return o_specific(0x01U);
    if (entries == 0U || entries > O_MAX_ENTRIES) return o_specific(0x02U);
    if (completion_valid == 0U) return o_specific(0x00U);
    if (existing != 0U) return o_specific(0x01U);
    return cosmos_nvme_admin_oracle_status_success();
}

unsigned int cosmos_nvme_admin_oracle_delete_sq_status(
    unsigned int negotiated, unsigned int existing, unsigned int nsid,
    unsigned int cdw10, unsigned int cdw11, unsigned int cdw12,
    unsigned int cdw13, unsigned int low1, unsigned int high1,
    unsigned int low2, unsigned int high2, unsigned int bytes) {
    if (nsid != 0U || (cdw10 >> 16U) != 0U || cdw11 != 0U ||
        cdw12 != 0U || cdw13 != 0U ||
        !o_no_payload(low1, high1, low2, high2, bytes) ||
        !o_queue_allowed(negotiated, cdw10 & 0xFFFFU) || existing == 0U) {
        return o_specific(0x01U);
    }
    return cosmos_nvme_admin_oracle_status_success();
}

unsigned int cosmos_nvme_admin_oracle_delete_cq_status(
    unsigned int negotiated, unsigned int existing, unsigned int dependent,
    unsigned int nsid, unsigned int cdw10, unsigned int cdw11,
    unsigned int cdw12, unsigned int cdw13, unsigned int low1,
    unsigned int high1, unsigned int low2, unsigned int high2,
    unsigned int bytes) {
    unsigned int status = cosmos_nvme_admin_oracle_delete_sq_status(
        negotiated, existing, nsid, cdw10, cdw11, cdw12, cdw13,
        low1, high1, low2, high2, bytes);
    if (status != cosmos_nvme_admin_oracle_status_success()) return status;
    return dependent != 0U ? o_specific(0x0CU) :
        cosmos_nvme_admin_oracle_status_success();
}

unsigned int cosmos_nvme_admin_oracle_abort_status(
    unsigned int negotiated, unsigned int sq_valid, unsigned int nsid,
    unsigned int cdw10, unsigned int cdw11, unsigned int cdw12,
    unsigned int cdw13) {
    unsigned int qid = cdw10 >> 16U;
    if (nsid != 0U || cdw11 != 0U || cdw12 != 0U || cdw13 != 0U)
        return cosmos_nvme_admin_oracle_status_generic(0x02U);
    if (qid != 0U && (!o_queue_allowed(negotiated, qid) || sq_valid == 0U))
        return o_specific(0x01U);
    return cosmos_nvme_admin_oracle_status_success();
}

unsigned int cosmos_nvme_admin_oracle_envelope_status(
    unsigned int invalid, unsigned int queue_id, unsigned int cid,
    unsigned int opcode, unsigned int low1, unsigned int high1,
    unsigned int low2, unsigned int high2, unsigned int bytes) {
    int payload_opcode;
    if (invalid != 0U || queue_id != 0U || cid > 0xFFFFU)
        return cosmos_nvme_admin_oracle_status_generic(0x02U);
    payload_opcode = opcode == 0x06U || opcode == 0x02U ||
        opcode == 0x01U || opcode == 0x05U;
    if (!o_no_payload(low1, high1, low2, high2, bytes) &&
        o_opcode(opcode) && !payload_opcode)
        return cosmos_nvme_admin_oracle_status_generic(0x02U);
    return O_CONTINUE;
}

unsigned int cosmos_nvme_admin_oracle_async_event_status(
    unsigned int callback, unsigned int pending, unsigned int nsid,
    unsigned int cdw10, unsigned int cdw11, unsigned int cdw12,
    unsigned int cdw13) {
    if (callback == 0U) return cosmos_nvme_admin_oracle_status_generic(0x01U);
    if (nsid != 0U || cdw10 != 0U || cdw11 != 0U || cdw12 != 0U ||
        cdw13 != 0U) return cosmos_nvme_admin_oracle_status_generic(0x02U);
    if (pending != 0U) return o_specific(0x05U);
    return O_CONTINUE;
}

int cosmos_nvme_admin_oracle_frozen_selfcheck(void) {
    return o_min(4U, 9U) == 4U && o_power_of_two(512U) &&
        o_log2(512U) == 9U && o_payload(
            0x1FFCU, 0U, 0x3000U, 0U, 8U, 8U) &&
        !o_payload(0x1FFCU, 0U, 0x3004U, 0U, 8U, 8U);
}

#ifdef COSMOS_NVME_ADMIN_ORACLE_BRIDGE
/* Test-only resolvers for C bridge contract tests. */
unsigned int cosmos_nvme_admin_policy_status_success(void) { return cosmos_nvme_admin_oracle_status_success(); }
unsigned int cosmos_nvme_admin_policy_status_generic(unsigned int sc) { return cosmos_nvme_admin_oracle_status_generic(sc); }
unsigned int cosmos_nvme_admin_policy_status_specific(unsigned int sc) { return o_specific(sc); }
unsigned int cosmos_nvme_admin_policy_min(unsigned int a, unsigned int b) { return o_min(a, b); }
int cosmos_nvme_admin_policy_power_of_two(unsigned int v) { return o_power_of_two(v); }
unsigned int cosmos_nvme_admin_policy_log2(unsigned int v) { return o_log2(v); }
int cosmos_nvme_admin_policy_no_payload(unsigned int a, unsigned int b, unsigned int c, unsigned int d, unsigned int e) { return o_no_payload(a, b, c, d, e); }
int cosmos_nvme_admin_policy_queue_base_valid(unsigned int a, unsigned int b, unsigned int c, unsigned int d, unsigned int e) { return o_queue_base(a, b, c, d, e); }
int cosmos_nvme_admin_policy_opcode_supported(unsigned int v) { return o_opcode(v); }
int cosmos_nvme_admin_policy_payload_valid(unsigned int a, unsigned int b, unsigned int c, unsigned int d, unsigned int e, unsigned int f) { return o_payload(a, b, c, d, e, f); }
int cosmos_nvme_admin_policy_queue_index_valid(unsigned int q) { return q != 0U && q <= O_MAX_QUEUES; }
int cosmos_nvme_admin_policy_queue_id_allowed(unsigned int n, unsigned int q) { return o_queue_allowed(n, q); }
int cosmos_nvme_admin_policy_controller_namespace_valid(unsigned int n) { return o_controller_nsid(n); }
int cosmos_nvme_admin_policy_smart_namespace_valid(unsigned int n) { return o_smart_nsid(n); }
unsigned int cosmos_nvme_admin_policy_publish_state(unsigned int r) { return r == 0U ? 0U : (r == 1U ? 1U : 2U); }
int cosmos_nvme_admin_policy_publish_result(unsigned int r) { return r == 0U ? 0 : (r == 1U ? 5 : (r == 2U ? 6 : 4)); }
unsigned int cosmos_nvme_admin_policy_payload_status(unsigned int v, unsigned int r) { return v != 0U && r == 0U ? cosmos_nvme_admin_oracle_status_success() : cosmos_nvme_admin_oracle_status_generic(0x04U); }
unsigned int cosmos_nvme_admin_policy_identify_status(unsigned int a, unsigned int b, unsigned int c, unsigned int d, unsigned int e) { return cosmos_nvme_admin_oracle_identify_status(a, b, c, d, e); }
unsigned int cosmos_nvme_admin_policy_get_log_status(unsigned int a, unsigned int b, unsigned int c, unsigned int d, unsigned int e) { return cosmos_nvme_admin_oracle_get_log_status(a, b, c, d, e); }
unsigned int cosmos_nvme_admin_policy_set_features_status(unsigned int a, unsigned int b, unsigned int c, unsigned int d, unsigned int e) { return cosmos_nvme_admin_oracle_set_features_status(a, b, c, d, e); }
unsigned int cosmos_nvme_admin_policy_queue_count(unsigned int v) { return o_min(O_MAX_QUEUES, o_min((v & 0xFFFFU) + 1U, (v >> 16U) + 1U)); }
unsigned int cosmos_nvme_admin_policy_queue_result(unsigned int v) { return (v - 1U) | ((v - 1U) << 16U); }
unsigned int cosmos_nvme_admin_policy_get_features_status(unsigned int a, unsigned int b, unsigned int c, unsigned int d, unsigned int e) { return cosmos_nvme_admin_oracle_get_features_status(a, b, c, d, e); }
unsigned int cosmos_nvme_admin_policy_create_cq_status(unsigned int a, unsigned int b, unsigned int c, unsigned int d, unsigned int e, unsigned int f, unsigned int g, unsigned int h, unsigned int i, unsigned int j, unsigned int k, unsigned int l) { return cosmos_nvme_admin_oracle_create_cq_status(a,b,c,d,e,f,g,h,i,j,k,l); }
unsigned int cosmos_nvme_admin_policy_create_sq_status(unsigned int a, unsigned int b, unsigned int c, unsigned int d, unsigned int e, unsigned int f, unsigned int g, unsigned int h, unsigned int i, unsigned int j, unsigned int k, unsigned int l, unsigned int m) { return cosmos_nvme_admin_oracle_create_sq_status(a,b,c,d,e,f,g,h,i,j,k,l,m); }
unsigned int cosmos_nvme_admin_policy_delete_sq_status(unsigned int a, unsigned int b, unsigned int c, unsigned int d, unsigned int e, unsigned int f, unsigned int g, unsigned int h, unsigned int i, unsigned int j, unsigned int k, unsigned int l) { return cosmos_nvme_admin_oracle_delete_sq_status(a,b,c,d,e,f,g,h,i,j,k,l); }
unsigned int cosmos_nvme_admin_policy_delete_cq_status(unsigned int a, unsigned int b, unsigned int c, unsigned int d, unsigned int e, unsigned int f, unsigned int g, unsigned int h, unsigned int i, unsigned int j, unsigned int k, unsigned int l, unsigned int m) { return cosmos_nvme_admin_oracle_delete_cq_status(a,b,c,d,e,f,g,h,i,j,k,l,m); }
unsigned int cosmos_nvme_admin_policy_abort_status(unsigned int a, unsigned int b, unsigned int c, unsigned int d, unsigned int e, unsigned int f, unsigned int g) { return cosmos_nvme_admin_oracle_abort_status(a,b,c,d,e,f,g); }
unsigned int cosmos_nvme_admin_policy_abort_result(unsigned int q, unsigned int cid, unsigned int p, unsigned int pcid) { return q == 0U && p != 0U && cid == pcid ? 0U : 1U; }
unsigned int cosmos_nvme_admin_policy_envelope_status(unsigned int a, unsigned int b, unsigned int c, unsigned int d, unsigned int e, unsigned int f, unsigned int g, unsigned int h, unsigned int i) { return cosmos_nvme_admin_oracle_envelope_status(a,b,c,d,e,f,g,h,i); }
unsigned int cosmos_nvme_admin_policy_async_event_status(unsigned int a, unsigned int b, unsigned int c, unsigned int d, unsigned int e, unsigned int f, unsigned int g) { return cosmos_nvme_admin_oracle_async_event_status(a,b,c,d,e,f,g); }
int cosmos_nvme_admin_policy_init_values_valid(unsigned int a, unsigned int b, unsigned int c) { return (a != 0U || b != 0U) && o_power_of_two(c); }
unsigned int cosmos_nvme_admin_policy_adapter_failure_status(int r) { return r == 0 ? cosmos_nvme_admin_oracle_status_success() : cosmos_nvme_admin_oracle_status_generic(0x06U); }
#endif
