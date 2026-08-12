//! Bounded, encoded process-transfer framing.
//!
//! Process boundaries never carry `RuntimeValue` bits. The payload is an
//! explicitly encoded byte sequence protected by an `SPTR` v1 envelope,
//! length bound, and checksum. Schema interpretation remains the caller's job.

use super::transfer::{RuntimeTransferEnvelopeV1, TransferDomain, TRANSFER_ENVELOPE_LEN};

pub(crate) const MAX_PROCESS_TRANSFER_BYTES: usize = 4 * 1024 * 1024;
const PROCESS_FRAME_HEADER_LEN: usize = TRANSFER_ENVELOPE_LEN + 16;

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct ProcessTransferFrame {
    envelope: RuntimeTransferEnvelopeV1,
    payload: Vec<u8>,
}

impl ProcessTransferFrame {
    pub(crate) fn encoded_copy(
        payload: Vec<u8>,
        source_domain: TransferDomain,
        target_domain: TransferDomain,
    ) -> Option<Self> {
        if payload.len() > MAX_PROCESS_TRANSFER_BYTES || !process_route_allowed(source_domain, target_domain) {
            return None;
        }
        Some(Self {
            envelope: RuntimeTransferEnvelopeV1::encoded_copy(source_domain, target_domain)?,
            payload,
        })
    }

    pub(crate) fn encode(&self) -> Option<Vec<u8>> {
        if self.payload.len() > MAX_PROCESS_TRANSFER_BYTES {
            return None;
        }
        let mut out = Vec::with_capacity(PROCESS_FRAME_HEADER_LEN + self.payload.len());
        out.extend_from_slice(&self.envelope.encode()?);
        out.extend_from_slice(&(self.payload.len() as u64).to_le_bytes());
        out.extend_from_slice(&payload_checksum(&self.payload).to_le_bytes());
        out.extend_from_slice(&self.payload);
        Some(out)
    }

    pub(crate) fn decode_for_target(bytes: &[u8], target: TransferDomain) -> Option<Self> {
        if bytes.len() < PROCESS_FRAME_HEADER_LEN {
            return None;
        }
        let envelope = RuntimeTransferEnvelopeV1::decode(&bytes[..TRANSFER_ENVELOPE_LEN])?;
        if envelope.target_domain() != target || !process_route_allowed(envelope.source_domain, envelope.target_domain)
        {
            return None;
        }
        let payload_len = u64::from_le_bytes(
            bytes[TRANSFER_ENVELOPE_LEN..TRANSFER_ENVELOPE_LEN + 8]
                .try_into()
                .ok()?,
        );
        if payload_len > MAX_PROCESS_TRANSFER_BYTES as u64
            || bytes.len() != PROCESS_FRAME_HEADER_LEN.checked_add(payload_len as usize)?
        {
            return None;
        }
        let expected_checksum = u64::from_le_bytes(
            bytes[TRANSFER_ENVELOPE_LEN + 8..PROCESS_FRAME_HEADER_LEN]
                .try_into()
                .ok()?,
        );
        let payload = bytes[PROCESS_FRAME_HEADER_LEN..].to_vec();
        (payload_checksum(&payload) == expected_checksum).then_some(Self { envelope, payload })
    }

    pub(crate) fn payload(&self) -> &[u8] {
        &self.payload
    }
}

fn process_route_allowed(source: TransferDomain, target: TransferDomain) -> bool {
    matches!(
        (source, target),
        (TransferDomain::Parent, TransferDomain::Process) | (TransferDomain::Process, TransferDomain::Parent)
    )
}

fn payload_checksum(payload: &[u8]) -> u64 {
    // Stable FNV-1a is corruption detection, not authentication. A future
    // authenticated remote transport must use the admitted wire hash contract.
    let mut hash = 0xcbf29ce484222325u64;
    for byte in payload {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::process::Command;

    fn reverse_payload(payload: &[u8]) -> Vec<u8> {
        payload.iter().rev().copied().collect()
    }

    #[test]
    #[ignore = "invoked as the isolated child by separate_process_uses_encoded_frames_in_both_directions"]
    fn process_transfer_child() {
        let Some(input_path) = std::env::var_os("SIMPLE_PROCESS_TRANSFER_TEST_INPUT") else {
            return;
        };
        let output_path = std::env::var_os("SIMPLE_PROCESS_TRANSFER_TEST_OUTPUT").unwrap();
        let encoded = std::fs::read(input_path).unwrap();
        let input = ProcessTransferFrame::decode_for_target(&encoded, TransferDomain::Process).unwrap();
        let output = ProcessTransferFrame::encoded_copy(
            reverse_payload(input.payload()),
            TransferDomain::Process,
            TransferDomain::Parent,
        )
        .unwrap();
        std::fs::write(output_path, output.encode().unwrap()).unwrap();
    }

    #[test]
    fn separate_process_uses_encoded_frames_in_both_directions() {
        let temp = tempfile::tempdir().unwrap();
        let input_path = temp.path().join("input.sptr");
        let output_path = temp.path().join("output.sptr");
        let input = ProcessTransferFrame::encoded_copy(
            b"parent-owned-bytes".to_vec(),
            TransferDomain::Parent,
            TransferDomain::Process,
        )
        .unwrap();
        std::fs::write(&input_path, input.encode().unwrap()).unwrap();

        let status = Command::new(std::env::current_exe().unwrap())
            .arg("--ignored")
            .arg("--exact")
            .arg("value::process_transfer::tests::process_transfer_child")
            .env("SIMPLE_PROCESS_TRANSFER_TEST_INPUT", &input_path)
            .env("SIMPLE_PROCESS_TRANSFER_TEST_OUTPUT", &output_path)
            .status()
            .unwrap();
        assert!(status.success());

        let encoded = std::fs::read(output_path).unwrap();
        let output = ProcessTransferFrame::decode_for_target(&encoded, TransferDomain::Parent).unwrap();
        assert_eq!(output.payload(), b"setyb-denwo-tnerap");
        assert_ne!(output.envelope.region_id, input.envelope.region_id);
    }

    #[test]
    fn process_frame_rejects_wrong_target_corruption_and_oversize() {
        let frame =
            ProcessTransferFrame::encoded_copy(b"typed".to_vec(), TransferDomain::Parent, TransferDomain::Process)
                .unwrap();
        let encoded = frame.encode().unwrap();
        assert!(ProcessTransferFrame::decode_for_target(&encoded, TransferDomain::Parent).is_none());

        let mut corrupt = encoded.clone();
        *corrupt.last_mut().unwrap() ^= 1;
        assert!(ProcessTransferFrame::decode_for_target(&corrupt, TransferDomain::Process).is_none());
        assert!(ProcessTransferFrame::encoded_copy(
            vec![0; MAX_PROCESS_TRANSFER_BYTES + 1],
            TransferDomain::Parent,
            TransferDomain::Process,
        )
        .is_none());
        assert!(ProcessTransferFrame::encoded_copy(
            b"wrong route".to_vec(),
            TransferDomain::Actor,
            TransferDomain::Process,
        )
        .is_none());
    }
}
