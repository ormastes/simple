//! Shared, allocation-free projection rules. No process authority is stored here.
use super::interactive_process_abi_v1::*;
use core::mem::size_of;

pub fn zero_receipt() -> Oiv1Receipt {
    let mut r: Oiv1Receipt = unsafe { core::mem::zeroed() };
    r.version = OIV1_VERSION; r.size = size_of::<Oiv1Receipt>() as u64; r
}
pub fn invalid_receipt() -> Oiv1Receipt {
    let mut r = zero_receipt(); r.status = OIV1_STATUS_INVALIDARGUMENT;
    r.validity_mask = OIV1_VALID_ERROR; r.error_domain = OIV1_ERROR_CONTRACT; r.error_code = 0; r
}
pub fn projection_failure(r: &mut Oiv1Receipt) {
    // Status describes the projector failure. The native error fields/validity
    // are captured owner facts, not space for invented projector subcodes.
    r.status = OIV1_STATUS_PROJECTIONFAILURE;
}
pub fn deadline(clock_tag: i64, expires_ms: i64) -> Oiv1Deadline {
    Oiv1Deadline { version: OIV1_VERSION, size: size_of::<Oiv1Deadline>() as u64,
        clock_tag: clock_tag as u64, expires_ms }
}
pub fn valid_receipt(r: &Oiv1Receipt, stdout_max: u64, stderr_max: u64) -> bool {
    r.version == OIV1_VERSION && r.size == size_of::<Oiv1Receipt>() as u64 &&
    r.status <= OIV1_STATUS_INVALIDARGUMENT && r.validity_mask & !255 == 0 &&
    r.phase <= OIV1_PHASE_FAILEDHELD && r.stdin_state <= OIV1_STREAM_FINISHREQUESTED &&
    r.stdout_state <= OIV1_STREAM_FINISHREQUESTED && r.stderr_state <= OIV1_STREAM_FINISHREQUESTED &&
    r.exit_kind <= OIV1_EXIT_FAILED && r.error_domain <= OIV1_ERROR_ABI && r.reserved0 == 0 &&
    r.stdout_count <= stdout_max && r.stderr_count <= stderr_max &&
    r.stdout_delivered_total >= r.stdout_count && r.stderr_delivered_total >= r.stderr_count
}
fn clear_private_projection(r: &mut Oiv1Receipt) {
    r.flags &= !(OIV1_FLAG_STARTPUBLICATIONPENDING | OIV1_FLAG_OUTPUTDELIVERYRESERVED | OIV1_FLAG_LOANPRESENT);
    r.ticket0 = 0; r.ticket1 = 0; r.ticket2 = 0; r.ticket3 = 0;
}
fn discard_conditional_output(r: &mut Oiv1Receipt) {
    // Raw poll totals include reserved bytes, conditional on COMMIT. ABORT
    // must not publish those totals as delivered.
    match (r.stdout_delivered_total.checked_sub(r.stdout_count), r.stderr_delivered_total.checked_sub(r.stderr_count)) {
        (Some(out), Some(err)) => { r.stdout_delivered_total = out; r.stderr_delivered_total = err; }
        _ => r.validity_mask &= !OIV1_VALID_COUNTS,
    }
    r.stdout_count = 0; r.stderr_count = 0; r.validity_mask &= !OIV1_VALID_OUTPUT;
}
/// Resolve once using the core's permanent-slot atomic intent word. The admitted
/// provider never returns ResolvingInProgress for a valid live ticket. An ABI
/// violation remains retained/fail-closed, never a usable uncommitted lease.
pub fn finish_projection(r: &mut Oiv1Receipt, commit: bool) -> bool {
    let ticket = Oiv1Ticket { word0: r.ticket0, word1: r.ticket1, word2: r.ticket2, word3: r.ticket3 };
    let has_ticket = ticket.word1 != 0 || ticket.word2 != 0 || ticket.word3 != 0;
    let reserved = r.flags & (OIV1_FLAG_STARTPUBLICATIONPENDING | OIV1_FLAG_OUTPUTDELIVERYRESERVED | OIV1_FLAG_LOANPRESENT) != 0;
    if !has_ticket {
        clear_private_projection(r);
        if reserved {
            projection_failure(r); discard_conditional_output(r);
            r.flags |= OIV1_FLAG_MAINTENANCEDEFERRED;
            return false;
        }
        if !commit { projection_failure(r); discard_conditional_output(r); }
        return commit;
    }
    let request = Oiv1ResolveRequest { version: OIV1_VERSION, size: size_of::<Oiv1ResolveRequest>() as u64,
        ticket, action: if commit { OIV1_ACTION_COMMIT } else { OIV1_ACTION_ABORT } };
    let result = unsafe { simple_owned_interactive_v1_resolve(&request, size_of::<Oiv1ResolveRequest>() as u64) };
    // Tickets are internal even when the provider violates the decision contract.
    clear_private_projection(r);
    if result == OIV1_RESOLVE_RECORDED as i64 || result == OIV1_RESOLVE_ALREADYSAME as i64 {
        if !commit { discard_conditional_output(r); projection_failure(r); }
        return commit;
    }
    // Cancellation can have won the same transaction. A bounded ABORT attempt
    // reconciles that case without locks/allocations or a shadow retry map.
    // Keep the allocated owner receipt even for a violated resolver contract.
    let abort = Oiv1ResolveRequest { action: OIV1_ACTION_ABORT, ..request };
    let abort_result = unsafe { simple_owned_interactive_v1_resolve(&abort, size_of::<Oiv1ResolveRequest>() as u64) };
    if abort_result == OIV1_RESOLVE_RECORDED as i64 || abort_result == OIV1_RESOLVE_ALREADYSAME as i64 {
        discard_conditional_output(r);
    } else {
        r.stdout_count = 0; r.stderr_count = 0;
        r.validity_mask &= !(OIV1_VALID_OUTPUT | OIV1_VALID_COUNTS);
    }
    projection_failure(r);
    if result == OIV1_RESOLVE_RESOLVINGINPROGRESS as i64 { r.status = OIV1_STATUS_RETAINEDCLEANUP; }
    r.flags |= OIV1_FLAG_MAINTENANCEDEFERRED;
    false
}
/// Complete unpublished typed storage before recording a transactional decision.
pub fn prepared_receipt_words(r: &Oiv1Receipt, publishable: bool) -> [u64; 32] {
    let mut prepared = *r;
    clear_private_projection(&mut prepared);
    if !publishable { discard_conditional_output(&mut prepared); projection_failure(&mut prepared); }
    receipt_words(&prepared)
}
pub fn receipt_words(r: &Oiv1Receipt) -> [u64; 32] {
    [r.version,r.size,r.status,r.validity_mask,r.handle_echo as u64,r.phase,r.stdin_state,r.stdout_state,
     r.stderr_state,r.exit_kind,r.exit_value as u64,r.error_domain,r.error_code,r.accepted_delta,
     r.accepted_total,r.written_total,r.stdin_queued,r.stdout_seen_total,r.stderr_seen_total,
     r.stdout_delivered_total,r.stderr_delivered_total,r.stdout_count,r.stderr_count,
     r.stdout_discarded_total,r.stderr_discarded_total,r.flags,r.operation_sequence,r.reserved0,0,0,0,0]
}
pub fn capability_words(c: &Oiv1Capabilities) -> [u64; 16] {
    [c.version,c.size,c.status,c.capability_mask,c.max_leases,c.stdin_capacity_max,c.stdout_capacity_max,
     c.stderr_capacity_max,c.write_quantum,c.output_chunk_max,c.poll_wait_max,c.segment_max,c.clock_tag,
     c.error_domain,c.error_code,c.reserved0]
}
pub fn deadline_words(d: &Oiv1Deadline, r: &Oiv1Receipt) -> [u64; 8] {
    [OIV1_VERSION,size_of::<Oiv1Deadline>() as u64,d.clock_tag,d.expires_ms as u64,r.status,r.error_domain,r.error_code,0]
}

#[cfg(test)]
mod protocol_tests {
    use super::*;
    #[test]
    fn interactive_protocol_no_ticket_reserved_failure_clears_private_state() {
        let mut receipt = zero_receipt();
        receipt.flags = OIV1_FLAG_OWNERHELD | OIV1_FLAG_STARTPUBLICATIONPENDING |
            OIV1_FLAG_OUTPUTDELIVERYRESERVED | OIV1_FLAG_LOANPRESENT;
        receipt.validity_mask = OIV1_VALID_OWNER | OIV1_VALID_PHASE | OIV1_VALID_COUNTS | OIV1_VALID_OUTPUT;
        receipt.handle_echo = 41; receipt.phase = OIV1_PHASE_STARTING;
        receipt.stdout_count = 3; receipt.stderr_count = 2;
        receipt.stdout_delivered_total = 8; receipt.stderr_delivered_total = 7;
        // Malformed provider observation: reserved flags but no decision ticket.
        // This branch performs no raw resolver/process call: it is a pure
        // protocol regression, not a simulated functional process success.
        assert!(!finish_projection(&mut receipt, true));
        let words = receipt_words(&receipt);
        assert_eq!(words[2], OIV1_STATUS_PROJECTIONFAILURE);
        assert_eq!(words[25] & (OIV1_FLAG_STARTPUBLICATIONPENDING |
            OIV1_FLAG_OUTPUTDELIVERYRESERVED | OIV1_FLAG_LOANPRESENT), 0);
        assert_eq!(&words[28..], &[0, 0, 0, 0]);
        assert_eq!(receipt.handle_echo, 41);
        assert_eq!(receipt.phase, OIV1_PHASE_STARTING);
        assert_ne!(receipt.flags & OIV1_FLAG_OWNERHELD, 0);
        assert_ne!(receipt.validity_mask & OIV1_VALID_OWNER, 0);
        assert_ne!(receipt.flags & OIV1_FLAG_MAINTENANCEDEFERRED, 0);
        assert_eq!(receipt.stdout_count, 0); assert_eq!(receipt.stderr_count, 0);
        assert_eq!(receipt.stdout_delivered_total, 5);
        assert_eq!(receipt.stderr_delivered_total, 5);
        assert_eq!(receipt.validity_mask & OIV1_VALID_OUTPUT, 0);
        assert_eq!(receipt.flags & (OIV1_FLAG_RESOURCESCLOSED | OIV1_FLAG_NOCHILDPROVEN | OIV1_FLAG_TREEEMPTY | OIV1_FLAG_REAPED), 0);
    }
}

#[cfg(test)]
mod native_error_tests {
    use super::*;
    #[test]
    fn interactive_protocol_projection_failure_preserves_native_error() {
        let mut receipt = zero_receipt();
        receipt.status = OIV1_STATUS_NATIVEFAILURE;
        receipt.validity_mask = OIV1_VALID_ERROR | OIV1_VALID_COUNTS;
        receipt.error_domain = OIV1_ERROR_WIN32; receipt.error_code = 87;
        receipt.accepted_total = 17; receipt.written_total = 11;
        projection_failure(&mut receipt);
        assert_eq!(receipt.status, OIV1_STATUS_PROJECTIONFAILURE);
        assert_eq!(receipt.error_domain, OIV1_ERROR_WIN32);
        assert_eq!(receipt.error_code, 87);
        assert_eq!(receipt.validity_mask, OIV1_VALID_ERROR | OIV1_VALID_COUNTS);
        assert_eq!(receipt.accepted_total, 17);
        assert_eq!(receipt.written_total, 11);
        assert_eq!(invalid_receipt().error_code, 0);
    }
}
