//! Native implementation of the frozen `TransferEnvelopeV1` wire contract.
//!
//! The 40-byte metadata prefix is byte-for-byte compatible with
//! `std.common.structural.transfer.transfer_codec`. Runtime-only inline copy
//! packets append eight payload bytes; heap addresses have no packet form.

use std::sync::atomic::{AtomicU64, Ordering};

use super::core::RuntimeValue;

pub(crate) const TRANSFER_SCHEMA_VERSION: u16 = 1;
pub(crate) const TRANSFER_ENVELOPE_LEN: usize = 40;
pub(crate) const TRANSFER_PACKET_LEN: usize = 48;
const TRANSFER_MAGIC: [u8; 4] = *b"SPTR";
static NEXT_TRANSFER_REGION_ID: AtomicU64 = AtomicU64::new(1);

#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TransferDomain {
    Parent = 0,
    Thread = 1,
    Process = 2,
    Actor = 3,
    Device = 4,
    Remote = 5,
}

#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TransferMode {
    Copy = 0,
    FrozenShare = 1,
    OwnedMove = 2,
    ScopedLoan = 3,
    Lease = 4,
}

#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TransferPayload {
    InlineCopy = 0,
    FrozenRegion = 1,
    OwnedRegion = 2,
    EncodedCopy = 3,
    ObjectHandle = 4,
    SharedSync = 5,
    DeviceLease = 6,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct RuntimeTransferEnvelopeV1 {
    pub region_id: u64,
    pub generation: u64,
    pub source_domain: TransferDomain,
    pub target_domain: TransferDomain,
    pub mode: TransferMode,
    pub payload: TransferPayload,
    pub ownership_token: u64,
    pub source_invalidated: bool,
}

impl RuntimeTransferEnvelopeV1 {
    pub(crate) fn boundary_allowed(self) -> bool {
        if self.region_id == 0 || self.region_id > i64::MAX as u64 || self.generation > i64::MAX as u64 {
            return false;
        }
        if self.source_domain == self.target_domain {
            return false;
        }
        if self.mode == TransferMode::OwnedMove {
            if self.payload != TransferPayload::OwnedRegion
                || self.ownership_token == 0
                || self.ownership_token > i64::MAX as u64
                || !self.source_invalidated
            {
                return false;
            }
        } else if self.ownership_token != 0 || self.source_invalidated {
            return false;
        }
        if self.mode == TransferMode::ScopedLoan
            && (self.payload != TransferPayload::ObjectHandle || self.target_domain != TransferDomain::Thread)
        {
            return false;
        }
        match self.target_domain {
            TransferDomain::Process | TransferDomain::Remote => {
                matches!(
                    self.payload,
                    TransferPayload::EncodedCopy | TransferPayload::ObjectHandle
                )
            }
            TransferDomain::Device => self.mode == TransferMode::Lease && self.payload == TransferPayload::DeviceLease,
            _ => match self.mode {
                TransferMode::Copy => {
                    matches!(self.payload, TransferPayload::InlineCopy | TransferPayload::EncodedCopy)
                }
                TransferMode::FrozenShare => {
                    matches!(
                        self.payload,
                        TransferPayload::FrozenRegion | TransferPayload::ObjectHandle
                    )
                }
                TransferMode::OwnedMove => self.payload == TransferPayload::OwnedRegion,
                TransferMode::ScopedLoan => {
                    self.target_domain == TransferDomain::Thread && self.payload == TransferPayload::ObjectHandle
                }
                TransferMode::Lease => false,
            },
        }
    }

    pub(crate) fn encode(self) -> Option<[u8; TRANSFER_ENVELOPE_LEN]> {
        if !self.boundary_allowed() {
            return None;
        }
        let mut out = [0u8; TRANSFER_ENVELOPE_LEN];
        out[0..4].copy_from_slice(&TRANSFER_MAGIC);
        out[4..6].copy_from_slice(&TRANSFER_SCHEMA_VERSION.to_le_bytes());
        out[8..16].copy_from_slice(&self.region_id.to_le_bytes());
        out[16..24].copy_from_slice(&self.generation.to_le_bytes());
        out[24] = self.source_domain as u8;
        out[25] = self.target_domain as u8;
        out[26] = self.mode as u8;
        out[27] = self.payload as u8;
        out[28..36].copy_from_slice(&self.ownership_token.to_le_bytes());
        out[36] = u8::from(self.source_invalidated);
        Some(out)
    }

    pub(crate) fn decode(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != TRANSFER_ENVELOPE_LEN
            || bytes[0..4] != TRANSFER_MAGIC
            || u16::from_le_bytes(bytes[4..6].try_into().ok()?) != TRANSFER_SCHEMA_VERSION
            || bytes[6] != 0
            || bytes[7] != 0
            || bytes[36] > 1
            || bytes[37..40] != [0, 0, 0]
        {
            return None;
        }
        let value = Self {
            region_id: u64::from_le_bytes(bytes[8..16].try_into().ok()?),
            generation: u64::from_le_bytes(bytes[16..24].try_into().ok()?),
            source_domain: TransferDomain::try_from(bytes[24]).ok()?,
            target_domain: TransferDomain::try_from(bytes[25]).ok()?,
            mode: TransferMode::try_from(bytes[26]).ok()?,
            payload: TransferPayload::try_from(bytes[27]).ok()?,
            ownership_token: u64::from_le_bytes(bytes[28..36].try_into().ok()?),
            source_invalidated: bytes[36] == 1,
        };
        value.boundary_allowed().then_some(value)
    }
}

macro_rules! impl_u8_enum {
    ($ty:ty, $($value:literal => $variant:path),+ $(,)?) => {
        impl TryFrom<u8> for $ty {
            type Error = ();
            fn try_from(value: u8) -> Result<Self, Self::Error> {
                match value { $($value => Ok($variant),)+ _ => Err(()) }
            }
        }
    };
}

impl_u8_enum!(TransferDomain, 0 => TransferDomain::Parent, 1 => TransferDomain::Thread,
    2 => TransferDomain::Process, 3 => TransferDomain::Actor, 4 => TransferDomain::Device,
    5 => TransferDomain::Remote);
impl_u8_enum!(TransferMode, 0 => TransferMode::Copy, 1 => TransferMode::FrozenShare,
    2 => TransferMode::OwnedMove, 3 => TransferMode::ScopedLoan, 4 => TransferMode::Lease);
impl_u8_enum!(TransferPayload, 0 => TransferPayload::InlineCopy, 1 => TransferPayload::FrozenRegion,
    2 => TransferPayload::OwnedRegion, 3 => TransferPayload::EncodedCopy,
    4 => TransferPayload::ObjectHandle, 5 => TransferPayload::SharedSync,
    6 => TransferPayload::DeviceLease);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct RuntimeTransferPacket {
    envelope: RuntimeTransferEnvelopeV1,
    inline_bits: u64,
}

impl RuntimeTransferPacket {
    pub(crate) fn inline_copy(
        value: RuntimeValue,
        source_domain: TransferDomain,
        target_domain: TransferDomain,
    ) -> Option<Self> {
        if !value.is_inline_transfer_value() {
            return None;
        }
        let region_id = NEXT_TRANSFER_REGION_ID.fetch_add(1, Ordering::Relaxed);
        if region_id == 0 || region_id > i64::MAX as u64 {
            return None;
        }
        let envelope = RuntimeTransferEnvelopeV1 {
            region_id,
            generation: 0,
            source_domain,
            target_domain,
            mode: TransferMode::Copy,
            payload: TransferPayload::InlineCopy,
            ownership_token: 0,
            source_invalidated: false,
        };
        envelope.boundary_allowed().then_some(Self {
            envelope,
            inline_bits: value.to_raw(),
        })
    }

    pub(crate) fn runtime_value(self) -> Option<RuntimeValue> {
        if self.envelope.mode != TransferMode::Copy || self.envelope.payload != TransferPayload::InlineCopy {
            return None;
        }
        let value = RuntimeValue::from_raw(self.inline_bits);
        value.is_inline_transfer_value().then_some(value)
    }

    pub(crate) fn runtime_value_for_target(self, target: TransferDomain) -> Option<RuntimeValue> {
        (self.envelope.target_domain == target)
            .then_some(())
            .and_then(|()| self.runtime_value())
    }

    pub(crate) fn encode(self) -> Option<[u8; TRANSFER_PACKET_LEN]> {
        let mut out = [0u8; TRANSFER_PACKET_LEN];
        out[..TRANSFER_ENVELOPE_LEN].copy_from_slice(&self.envelope.encode()?);
        out[TRANSFER_ENVELOPE_LEN..].copy_from_slice(&self.inline_bits.to_le_bytes());
        Some(out)
    }

    pub(crate) fn decode(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != TRANSFER_PACKET_LEN {
            return None;
        }
        let packet = Self {
            envelope: RuntimeTransferEnvelopeV1::decode(&bytes[..TRANSFER_ENVELOPE_LEN])?,
            inline_bits: u64::from_le_bytes(bytes[TRANSFER_ENVELOPE_LEN..].try_into().ok()?),
        };
        packet.runtime_value()?;
        Some(packet)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn transfer_envelope_matches_simple_golden_vector() {
        let envelope = RuntimeTransferEnvelopeV1 {
            region_id: 7,
            generation: 2,
            source_domain: TransferDomain::Parent,
            target_domain: TransferDomain::Thread,
            mode: TransferMode::OwnedMove,
            payload: TransferPayload::OwnedRegion,
            ownership_token: 99,
            source_invalidated: true,
        };
        let encoded = envelope.encode().unwrap();
        assert_eq!(
            encoded,
            [
                0x53, 0x50, 0x54, 0x52, 0x01, 0x00, 0x00, 0x00, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x02, 0x02, 0x63, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x01, 0x00, 0x00, 0x00,
            ]
        );
        assert_eq!(RuntimeTransferEnvelopeV1::decode(&encoded), Some(envelope));
    }

    #[test]
    fn transfer_packet_rejects_reserved_and_heap_bits() {
        let packet = RuntimeTransferPacket::inline_copy(
            RuntimeValue::from_int(42),
            TransferDomain::Parent,
            TransferDomain::Actor,
        )
        .unwrap();
        let mut encoded = packet.encode().unwrap();
        encoded[37] = 1;
        assert!(RuntimeTransferPacket::decode(&encoded).is_none());
        assert!(RuntimeTransferPacket::inline_copy(
            RuntimeValue::from_raw(0x1001),
            TransferDomain::Parent,
            TransferDomain::Actor
        )
        .is_none());
        assert!(RuntimeTransferPacket::inline_copy(
            RuntimeValue::from_raw(0x1004),
            TransferDomain::Parent,
            TransferDomain::Actor
        )
        .is_none());
    }
}
