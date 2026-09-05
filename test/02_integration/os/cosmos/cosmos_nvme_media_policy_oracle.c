/* Frozen independent C oracle from the pre-migration NVMe/media decisions. */
#include "cosmos_nvme_media_policy_oracle.h"

#define O_OK 0
#define O_UNAVAILABLE 1
#define O_INVALID 2
#define O_HW_ERROR 4
#define O_RETRY 5
#define O_UNCERTAIN 6
#define O_NSID 1U
#define O_MAX_CID 0xFFFFU
#define O_MAX_NLB 0xFFFFU
#define O_MAX_RANGES 256U
#define O_RANGE_BYTES 16U
#define O_BLOCK_BYTES 4096U
#define O_PAGE_BYTES 16384U
#define O_SPARE_BYTES 256U
#define O_PAGE_LBAS 4U
#define O_MAX_MEDIA_LBAS 256U
#define O_SLOT_MASK 0x7FU

static unsigned int o_status(unsigned int sct, unsigned int sc,
                             unsigned int dnr) {
    return (dnr << 16U) | (sct << 8U) | sc;
}

unsigned int cosmos_nvme_media_oracle_status_success(void) {
    return o_status(0U, 0U, 0U);
}

unsigned int cosmos_nvme_media_oracle_status_invalid_opcode(void) {
    return o_status(0U, 0x01U, 1U);
}

unsigned int cosmos_nvme_media_oracle_status_invalid_field(void) {
    return o_status(0U, 0x02U, 1U);
}

unsigned int cosmos_nvme_media_oracle_status_invalid_namespace(void) {
    return o_status(0U, 0x0BU, 1U);
}

unsigned int cosmos_nvme_media_oracle_status_lba_range(void) {
    return o_status(0U, 0x80U, 1U);
}

unsigned int cosmos_nvme_media_oracle_status_data_transfer(void) {
    return o_status(0U, 0x04U, 1U);
}

int cosmos_nvme_media_oracle_status_is_success(unsigned int encoded) {
    return encoded == cosmos_nvme_media_oracle_status_success();
}

unsigned int cosmos_nvme_media_oracle_media_status(
    int result, unsigned int media_sc) {
    if (result == O_OK) return cosmos_nvme_media_oracle_status_success();
    if (result == O_UNAVAILABLE) return o_status(0U, 0x82U, 0U);
    if (result == 3 || result == O_HW_ERROR) {
        return o_status(2U, media_sc, 0U);
    }
    return o_status(0U, 0x06U, 0U);
}

unsigned long long cosmos_nvme_media_oracle_u64(
    unsigned int low, unsigned int high) {
    return ((unsigned long long)high << 32U) | low;
}

int cosmos_nvme_media_oracle_end_within_namespace(
    unsigned int namespace_low, unsigned int namespace_high,
    unsigned int lba_low, unsigned int lba_high,
    unsigned int block_count) {
    unsigned int end_low = lba_low + block_count;
    unsigned int carry = end_low < lba_low;
    unsigned int end_high = lba_high + carry;
    if (end_high < lba_high) return 0;
    if (end_high != namespace_high) return end_high < namespace_high;
    return end_low <= namespace_low;
}

int cosmos_nvme_media_oracle_data_span_valid(
    unsigned int address_low, unsigned int address_high,
    unsigned int address2_low, unsigned int address2_high,
    unsigned int data_bytes, unsigned int required_bytes) {
    int second = address2_low != 0U || address2_high != 0U;
    if (address_low == 0U && address_high == 0U) return 0;
    if ((address_low & 3U) != 0U) return 0;
    if (second && (address2_low & 3U) != 0U) return 0;
    return data_bytes == required_bytes;
}

unsigned int cosmos_nvme_media_oracle_rw_status(
    unsigned int cid, unsigned int namespace_id,
    unsigned int lba_low, unsigned int lba_high, unsigned int nlb,
    unsigned int control, unsigned int address_low,
    unsigned int address_high, unsigned int address2_low,
    unsigned int address2_high, unsigned int data_bytes,
    unsigned int namespace_low, unsigned int namespace_high,
    unsigned int block_bytes) {
    unsigned int count;
    if (cid > O_MAX_CID || nlb > O_MAX_NLB ||
        (control & ~0xC0000000U) != 0U) {
        return cosmos_nvme_media_oracle_status_invalid_field();
    }
    if (namespace_id != O_NSID) {
        return cosmos_nvme_media_oracle_status_invalid_namespace();
    }
    count = nlb + 1U;
    if (!cosmos_nvme_media_oracle_end_within_namespace(
            namespace_low, namespace_high, lba_low, lba_high, count)) {
        return cosmos_nvme_media_oracle_status_lba_range();
    }
    if (block_bytes == 0U || count > (~0U / block_bytes) ||
        !cosmos_nvme_media_oracle_data_span_valid(
            address_low, address_high, address2_low, address2_high,
            data_bytes, count * block_bytes)) {
        return cosmos_nvme_media_oracle_status_data_transfer();
    }
    return cosmos_nvme_media_oracle_status_success();
}

unsigned int cosmos_nvme_media_oracle_flush_status(
    unsigned int cid, unsigned int namespace_id,
    unsigned int lba_low, unsigned int lba_high, unsigned int nlb,
    unsigned int address_low, unsigned int address_high,
    unsigned int address2_low, unsigned int address2_high,
    unsigned int data_bytes) {
    if (namespace_id != O_NSID) {
        return cosmos_nvme_media_oracle_status_invalid_namespace();
    }
    if (cid > O_MAX_CID || lba_low != 0U || lba_high != 0U || nlb != 0U ||
        address_low != 0U || address_high != 0U || address2_low != 0U ||
        address2_high != 0U || data_bytes != 0U) {
        return cosmos_nvme_media_oracle_status_invalid_field();
    }
    return cosmos_nvme_media_oracle_status_success();
}

unsigned int cosmos_nvme_media_oracle_zeroes_status(
    unsigned int cid, unsigned int namespace_id,
    unsigned int lba_low, unsigned int lba_high, unsigned int nlb,
    unsigned int control, unsigned int dataset_attributes,
    unsigned int dataset_range_count, unsigned int address_low,
    unsigned int address_high, unsigned int address2_low,
    unsigned int address2_high, unsigned int data_bytes,
    unsigned int namespace_low, unsigned int namespace_high,
    unsigned int callback_present) {
    if (namespace_id != O_NSID) {
        return cosmos_nvme_media_oracle_status_invalid_namespace();
    }
    if (cid > O_MAX_CID || nlb > O_MAX_NLB ||
        (control & ~0xC2000000U) != 0U || dataset_attributes != 0U ||
        dataset_range_count != 0U || address_low != 0U ||
        address_high != 0U || address2_low != 0U ||
        address2_high != 0U || data_bytes != 0U) {
        return cosmos_nvme_media_oracle_status_invalid_field();
    }
    if (!cosmos_nvme_media_oracle_end_within_namespace(
            namespace_low, namespace_high, lba_low, lba_high, nlb + 1U)) {
        return cosmos_nvme_media_oracle_status_lba_range();
    }
    if (callback_present == 0U) {
        return cosmos_nvme_media_oracle_status_invalid_opcode();
    }
    return cosmos_nvme_media_oracle_status_success();
}

unsigned int cosmos_nvme_media_oracle_dsm_status(
    unsigned int cid, unsigned int namespace_id,
    unsigned int lba_low, unsigned int lba_high, unsigned int nlb,
    unsigned int control, unsigned int dataset_attributes,
    unsigned int dataset_range_count, unsigned int address_low,
    unsigned int address_high, unsigned int address2_low,
    unsigned int address2_high, unsigned int data_bytes,
    unsigned int callback_present) {
    unsigned int required;
    if (namespace_id != O_NSID) {
        return cosmos_nvme_media_oracle_status_invalid_namespace();
    }
    if (cid > O_MAX_CID || dataset_range_count == 0U ||
        dataset_range_count > O_MAX_RANGES ||
        (dataset_attributes & ~7U) != 0U || lba_low != 0U ||
        lba_high != 0U || nlb != 0U || control != 0U) {
        return cosmos_nvme_media_oracle_status_invalid_field();
    }
    required = dataset_range_count * O_RANGE_BYTES;
    if (!cosmos_nvme_media_oracle_data_span_valid(
            address_low, address_high, address2_low, address2_high,
            data_bytes, required)) {
        return cosmos_nvme_media_oracle_status_data_transfer();
    }
    if ((dataset_attributes & 4U) == 0U) {
        return cosmos_nvme_media_oracle_status_success();
    }
    if (callback_present == 0U) {
        return cosmos_nvme_media_oracle_status_invalid_opcode();
    }
    return cosmos_nvme_media_oracle_status_success();
}

unsigned int cosmos_nvme_media_oracle_post_state(unsigned int post_result) {
    if (post_result == 0U) return 0U;
    if (post_result == 1U) return 1U;
    return 2U;
}

int cosmos_nvme_media_oracle_post_status(unsigned int post_result) {
    if (post_result == 0U) return O_OK;
    if (post_result == 1U) return O_RETRY;
    if (post_result == 2U) return O_UNCERTAIN;
    return O_HW_ERROR;
}

int cosmos_nvme_media_oracle_service_init_valid(
    unsigned int post_present, unsigned int read_present,
    unsigned int program_present, unsigned int flush_present,
    unsigned int namespace_low, unsigned int namespace_high,
    unsigned int block_bytes) {
    if (post_present == 0U || read_present == 0U ||
        program_present == 0U || flush_present == 0U) return 0;
    if (namespace_low == 0U && namespace_high == 0U) return 0;
    return block_bytes != 0U && (block_bytes & 3U) == 0U;
}

int cosmos_nvme_media_oracle_dispatch_init_valid(
    unsigned int dispatch_present, unsigned int bridge_present,
    unsigned int io_present, unsigned int admin_present,
    unsigned int io_fetch_present, unsigned int admin_fetch_present) {
    return dispatch_present != 0U && bridge_present != 0U &&
        io_present != 0U && admin_present != 0U && io_fetch_present == 0U &&
        admin_fetch_present == 0U;
}

int cosmos_nvme_media_oracle_dispatch_queue_status(
    unsigned int queue_id, unsigned int negotiated_queue_count,
    unsigned int submission_valid, unsigned int completion_queue_id,
    unsigned int completion_valid) {
    if (queue_id == 0U || queue_id > negotiated_queue_count ||
        queue_id > 4U || submission_valid == 0U ||
        completion_queue_id == 0U || completion_queue_id > 4U ||
        completion_valid == 0U) return O_HW_ERROR;
    return O_OK;
}

int cosmos_nvme_media_oracle_address_set_valid(
    unsigned int data_address, unsigned int spare_address,
    unsigned int completion_address, unsigned int status_report_address,
    unsigned int error_info_address) {
    return data_address != 0U && (data_address & (O_PAGE_BYTES - 1U)) == 0U &&
        spare_address != 0U &&
        (spare_address & (O_SPARE_BYTES - 1U)) == 0U &&
        completion_address != 0U && (completion_address & 3U) == 0U &&
        status_report_address != 0U && (status_report_address & 3U) == 0U &&
        error_info_address != 0U && (error_info_address & 3U) == 0U;
}

int cosmos_nvme_media_oracle_command_span_status(
    unsigned int media_present, unsigned int command_present,
    unsigned int namespace_id, unsigned int data_bytes,
    unsigned int slot_tag, unsigned int lba_low, unsigned int lba_high,
    unsigned int namespace_low, unsigned int namespace_high) {
    unsigned int count;
    unsigned long long lba;
    unsigned long long end_lba;
    if (media_present == 0U || command_present == 0U ||
        namespace_id != O_NSID || data_bytes == 0U ||
        (data_bytes % O_BLOCK_BYTES) != 0U) return O_INVALID;
    count = data_bytes / O_BLOCK_BYTES;
    if (count > O_MAX_MEDIA_LBAS ||
        slot_tag > O_SLOT_MASK) return O_INVALID;
    lba = cosmos_nvme_media_oracle_u64(lba_low, lba_high);
    end_lba = lba + count;
    if (end_lba < lba || end_lba > cosmos_nvme_media_oracle_u64(
            namespace_low, namespace_high)) return O_INVALID;
    return O_OK;
}

int cosmos_nvme_media_oracle_zeroes_span_status(
    unsigned int media_present, unsigned int command_present,
    unsigned int namespace_id, unsigned int data_bytes,
    unsigned int slot_tag, unsigned int lba_low, unsigned int lba_high,
    unsigned int nlb, unsigned int namespace_low,
    unsigned int namespace_high) {
    unsigned int count;
    unsigned long long lba;
    unsigned long long end_lba;
    if (media_present == 0U || command_present == 0U ||
        namespace_id != O_NSID || data_bytes != 0U) return O_INVALID;
    count = nlb + 1U;
    if (count == 0U || count > O_MAX_MEDIA_LBAS ||
        slot_tag > O_SLOT_MASK) return O_INVALID;
    lba = cosmos_nvme_media_oracle_u64(lba_low, lba_high);
    end_lba = lba + count;
    if (end_lba < lba || end_lba > cosmos_nvme_media_oracle_u64(
            namespace_low, namespace_high)) return O_INVALID;
    return O_OK;
}

unsigned int cosmos_nvme_media_oracle_retry_limit(unsigned int configured) {
    return configured == 0U ? 3U : configured;
}

unsigned int cosmos_nvme_media_oracle_command_retry_limit(
    unsigned int control, unsigned int limited_retry_mask) {
    return (control & limited_retry_mask) != 0U ? 1U : 3U;
}

int cosmos_nvme_media_oracle_begin_status(
    unsigned int media_present, unsigned int ftl_present,
    unsigned int prior_busy) {
    return media_present == 0U || ftl_present == 0U || prior_busy != 0U
        ? O_RETRY : O_OK;
}

int cosmos_nvme_media_oracle_retry_terminal(
    int status, unsigned int attempt, unsigned int limit) {
    return status != O_RETRY || attempt + 1U == limit;
}

int cosmos_nvme_media_oracle_mapped_read_status(
    int status, unsigned int actual_lpn, unsigned int expected_lpn) {
    return status == O_OK && actual_lpn != expected_lpn ? O_HW_ERROR : status;
}

int cosmos_nvme_media_oracle_dma_offsets_valid(
    unsigned int command_offset, unsigned int device_offset) {
    return command_offset <= 255U && device_offset < O_PAGE_LBAS;
}

unsigned int cosmos_nvme_media_oracle_page_action(
    int lookup_status, unsigned int write,
    unsigned int page_offset, unsigned int page_count) {
    if (lookup_status != O_OK && lookup_status != O_UNAVAILABLE) {
        return COSMOS_NVME_MEDIA_ORACLE_PAGE_PROPAGATE;
    }
    if (write != 0U && page_offset == 0U && page_count == O_PAGE_LBAS) {
        return COSMOS_NVME_MEDIA_ORACLE_PAGE_FULL_WRITE;
    }
    if (lookup_status == O_OK) {
        return COSMOS_NVME_MEDIA_ORACLE_PAGE_READ_MAPPED;
    }
    return COSMOS_NVME_MEDIA_ORACLE_PAGE_ZERO_UNMAPPED;
}

unsigned int cosmos_nvme_media_oracle_page_count(
    unsigned int page_offset, unsigned int remaining) {
    unsigned int available = O_PAGE_LBAS - page_offset;
    return available > remaining ? remaining : available;
}

int cosmos_nvme_media_oracle_dsm_range_valid(
    unsigned int attributes, unsigned int length,
    unsigned long long starting_lba,
    unsigned int namespace_low, unsigned int namespace_high) {
    unsigned long long end_lba;
    if (attributes != 0U || length == 0U) return 0;
    end_lba = starting_lba + length;
    return end_lba >= starting_lba && end_lba <=
        cosmos_nvme_media_oracle_u64(namespace_low, namespace_high);
}

int cosmos_nvme_media_oracle_init_valid(
    unsigned int media_present, unsigned int ftl_present,
    unsigned int data_address, unsigned int spare_address,
    unsigned int completion_address, unsigned int status_report_address,
    unsigned int error_info_address) {
    return media_present != 0U && ftl_present != 0U &&
        cosmos_nvme_media_oracle_address_set_valid(
            data_address, spare_address, completion_address,
            status_report_address, error_info_address);
}

int cosmos_nvme_media_oracle_deallocate_valid(
    unsigned int media_present, unsigned int command_present,
    unsigned int namespace_id, unsigned int dataset_attributes,
    unsigned int dataset_range_count, unsigned int data_bytes,
    unsigned int slot_tag) {
    return media_present != 0U && command_present != 0U &&
        namespace_id == O_NSID && (dataset_attributes & 4U) != 0U &&
        (dataset_attributes & ~7U) == 0U && dataset_range_count != 0U &&
        dataset_range_count <= O_MAX_RANGES &&
        data_bytes == dataset_range_count * O_RANGE_BYTES &&
        slot_tag <= O_SLOT_MASK;
}

unsigned int cosmos_nvme_media_oracle_chunk_bytes(unsigned int remaining) {
    return remaining > O_PAGE_BYTES ? O_PAGE_BYTES : remaining;
}

int cosmos_nvme_media_oracle_full_page(unsigned int page_offset,
                                        unsigned int page_count) {
    return page_offset == 0U && page_count == O_PAGE_LBAS;
}
