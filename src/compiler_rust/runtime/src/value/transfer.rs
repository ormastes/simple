//! Native implementation of the frozen `TransferEnvelopeV1` wire contract.
//!
//! The 40-byte metadata prefix is byte-for-byte compatible with
//! `std.common.structural.transfer.transfer_codec`. Runtime-only inline copy
//! packets append eight payload bytes; heap addresses have no packet form.

use std::sync::atomic::{AtomicU64, Ordering};

use super::collections::{rt_string_new, RuntimeString};
use super::core::RuntimeValue;
use super::heap::{registered_heap_type, with_typed_ptr, HeapFloat, HeapObjectType, HeapUInt};

pub(crate) const TRANSFER_SCHEMA_VERSION: u16 = 1;
pub(crate) const TRANSFER_ENVELOPE_LEN: usize = 40;
pub(crate) const TRANSFER_PACKET_LEN: usize = 48;
pub(crate) const MAX_ENCODED_COPY_BYTES: usize = 1024 * 1024;
const ENCODED_COPY_HEADER_LEN: usize = TRANSFER_ENVELOPE_LEN + 24;
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

/// Static runtime classification at a safe execution-domain boundary.
///
/// This deliberately does not equate "registered heap pointer" with
/// transferable ownership. Heap graphs need a typed codec, frozen handle, or
/// a region-registry move; unknown/forged heap identity is rejected outright.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RuntimeTransferClass {
    InlineCopy,
    SharedSynchronizedHandle,
    HeapGraphRequiresCodec,
    InvalidHeapIdentity,
    UnsupportedBoundary,
}

pub(crate) fn classify_runtime_value(value: RuntimeValue, target: TransferDomain) -> RuntimeTransferClass {
    if target == TransferDomain::Device || target == TransferDomain::Remote {
        return RuntimeTransferClass::UnsupportedBoundary;
    }
    if value.is_inline_transfer_value() {
        return RuntimeTransferClass::InlineCopy;
    }
    let Some(heap_type) = registered_heap_type(value) else {
        return RuntimeTransferClass::InvalidHeapIdentity;
    };
    if heap_type == HeapObjectType::Channel && matches!(target, TransferDomain::Thread | TransferDomain::Actor) {
        return RuntimeTransferClass::SharedSynchronizedHandle;
    }
    RuntimeTransferClass::HeapGraphRequiresCodec
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
    pub(crate) fn encoded_copy(source_domain: TransferDomain, target_domain: TransferDomain) -> Option<Self> {
        let region_id = next_transfer_region_id()?;
        let envelope = Self {
            region_id,
            generation: 0,
            source_domain,
            target_domain,
            mode: TransferMode::Copy,
            payload: TransferPayload::EncodedCopy,
            ownership_token: 0,
            source_invalidated: false,
        };
        envelope.boundary_allowed().then_some(envelope)
    }

    pub(crate) fn target_domain(self) -> TransferDomain {
        self.target_domain
    }

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

#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum EncodedLeafKind {
    Float64 = 1,
    UInt64 = 2,
    Utf8 = 3,
    /// Full-width SIGNED i64 leaf (`HeapObjectType::Int`). Distinct from
    /// `UInt64` so a wide negative value does not round-trip as a huge
    /// positive one.
    Int64 = 4,
}

impl TryFrom<u8> for EncodedLeafKind {
    type Error = ();

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            1 => Ok(Self::Float64),
            2 => Ok(Self::UInt64),
            3 => Ok(Self::Utf8),
            4 => Ok(Self::Int64),
            _ => Err(()),
        }
    }
}

/// A bounded logical copy of one admitted heap leaf.
///
/// No runtime heap address is retained in this value or emitted on the wire.
/// Reachable graphs require a separate schema-aware graph codec.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RuntimeEncodedCopy {
    envelope: RuntimeTransferEnvelopeV1,
    kind: EncodedLeafKind,
    payload: Vec<u8>,
}

impl RuntimeEncodedCopy {
    pub(crate) fn from_value(
        value: RuntimeValue,
        source_domain: TransferDomain,
        target_domain: TransferDomain,
    ) -> Option<Self> {
        if matches!(target_domain, TransferDomain::Device | TransferDomain::Remote) {
            return None;
        }
        let heap_type = registered_heap_type(value)?;
        let (kind, payload) = match heap_type {
            HeapObjectType::Float => (
                EncodedLeafKind::Float64,
                with_typed_ptr::<HeapFloat, _>(value, HeapObjectType::Float, |ptr| unsafe {
                    (*ptr).value.to_bits().to_le_bytes().to_vec()
                })?,
            ),
            HeapObjectType::UInt => (
                EncodedLeafKind::UInt64,
                with_typed_ptr::<HeapUInt, _>(value, HeapObjectType::UInt, |ptr| unsafe {
                    (*ptr).value.to_le_bytes().to_vec()
                })?,
            ),
            HeapObjectType::Int => (
                EncodedLeafKind::Int64,
                with_typed_ptr::<crate::value::heap::HeapInt, _>(value, HeapObjectType::Int, |ptr| unsafe {
                    (*ptr).value.to_le_bytes().to_vec()
                })?,
            ),
            HeapObjectType::String => (
                EncodedLeafKind::Utf8,
                with_typed_ptr::<RuntimeString, _>(value, HeapObjectType::String, |ptr| unsafe {
                    (*ptr).as_bytes().to_vec()
                })?,
            ),
            _ => return None,
        };
        if payload.len() > MAX_ENCODED_COPY_BYTES
            || (kind == EncodedLeafKind::Utf8 && std::str::from_utf8(&payload).is_err())
        {
            return None;
        }
        Some(Self {
            envelope: RuntimeTransferEnvelopeV1::encoded_copy(source_domain, target_domain)?,
            kind,
            payload,
        })
    }

    pub(crate) fn encode(&self) -> Option<Vec<u8>> {
        if !self.payload_is_valid() {
            return None;
        }
        let mut out = Vec::with_capacity(ENCODED_COPY_HEADER_LEN + self.payload.len());
        out.extend_from_slice(&self.envelope.encode()?);
        out.push(self.kind as u8);
        out.extend_from_slice(&[0; 7]);
        out.extend_from_slice(&(self.payload.len() as u64).to_le_bytes());
        out.extend_from_slice(&encoded_copy_checksum(self.kind, &self.payload).to_le_bytes());
        out.extend_from_slice(&self.payload);
        Some(out)
    }

    pub(crate) fn decode_for_target(bytes: &[u8], target: TransferDomain) -> Option<Self> {
        if bytes.len() < ENCODED_COPY_HEADER_LEN {
            return None;
        }
        let envelope = RuntimeTransferEnvelopeV1::decode(&bytes[..TRANSFER_ENVELOPE_LEN])?;
        if envelope.target_domain != target
            || envelope.mode != TransferMode::Copy
            || envelope.payload != TransferPayload::EncodedCopy
        {
            return None;
        }
        let kind = EncodedLeafKind::try_from(bytes[TRANSFER_ENVELOPE_LEN]).ok()?;
        if bytes[TRANSFER_ENVELOPE_LEN + 1..TRANSFER_ENVELOPE_LEN + 8] != [0; 7] {
            return None;
        }
        let payload_len = u64::from_le_bytes(bytes[48..56].try_into().ok()?);
        if payload_len > MAX_ENCODED_COPY_BYTES as u64
            || bytes.len() != ENCODED_COPY_HEADER_LEN.checked_add(payload_len as usize)?
        {
            return None;
        }
        let expected_checksum = u64::from_le_bytes(bytes[56..64].try_into().ok()?);
        let value = Self {
            envelope,
            kind,
            payload: bytes[ENCODED_COPY_HEADER_LEN..].to_vec(),
        };
        (value.payload_is_valid() && encoded_copy_checksum(kind, &value.payload) == expected_checksum)
            .then_some(value)
    }

    pub(crate) fn materialize(&self) -> Option<RuntimeValue> {
        if !self.payload_is_valid() {
            return None;
        }
        match self.kind {
            EncodedLeafKind::Float64 => Some(RuntimeValue::from_float(f64::from_bits(u64::from_le_bytes(
                self.payload.as_slice().try_into().ok()?,
            )))),
            EncodedLeafKind::UInt64 => Some(RuntimeValue::from_u64(u64::from_le_bytes(
                self.payload.as_slice().try_into().ok()?,
            ))),
            EncodedLeafKind::Int64 => Some(RuntimeValue::from_int(i64::from_le_bytes(
                self.payload.as_slice().try_into().ok()?,
            ))),
            EncodedLeafKind::Utf8 => {
                std::str::from_utf8(&self.payload).ok()?;
                Some(rt_string_new(self.payload.as_ptr(), self.payload.len() as u64))
            }
        }
    }

    fn payload_is_valid(&self) -> bool {
        if self.payload.len() > MAX_ENCODED_COPY_BYTES {
            return false;
        }
        match self.kind {
            EncodedLeafKind::Float64 | EncodedLeafKind::UInt64 | EncodedLeafKind::Int64 => self.payload.len() == 8,
            EncodedLeafKind::Utf8 => std::str::from_utf8(&self.payload).is_ok(),
        }
    }
}

fn encoded_copy_checksum(kind: EncodedLeafKind, payload: &[u8]) -> u64 {
    let mut hash = 0xcbf29ce484222325u64;
    hash ^= kind as u64;
    hash = hash.wrapping_mul(0x100000001b3);
    for byte in payload {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash
}

impl RuntimeTransferPacket {
    pub(crate) fn inline_copy(
        value: RuntimeValue,
        source_domain: TransferDomain,
        target_domain: TransferDomain,
    ) -> Option<Self> {
        if classify_runtime_value(value, target_domain) != RuntimeTransferClass::InlineCopy {
            return None;
        }
        let region_id = next_transfer_region_id()?;
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

fn next_transfer_region_id() -> Option<u64> {
    // Fork duplicates process memory, including atomic counters. Namespace the
    // low 32-bit sequence by the current PID so parent and child cannot mint
    // the same region id after a fork.
    let sequence = NEXT_TRANSFER_REGION_ID.fetch_add(1, Ordering::Relaxed);
    if sequence == 0 || sequence > u32::MAX as u64 {
        return None;
    }
    let process = u64::from(std::process::id()) & 0x7fff_ffff;
    let region_id = (process << 32) | sequence;
    (region_id > 0 && region_id <= i64::MAX as u64).then_some(region_id)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::{rt_array_free, rt_array_new, rt_string_free};

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

    #[test]
    fn runtime_classification_distinguishes_invalid_and_registered_heap_identity() {
        assert_eq!(
            classify_runtime_value(RuntimeValue::from_raw(0x1001), TransferDomain::Thread),
            RuntimeTransferClass::InvalidHeapIdentity
        );
        let array = crate::value::rt_array_new(1);
        assert_eq!(
            classify_runtime_value(array, TransferDomain::Thread),
            RuntimeTransferClass::HeapGraphRequiresCodec
        );
        crate::value::rt_array_free(array);
    }

    #[test]
    fn runtime_classification_never_treats_device_input_as_host_copy() {
        assert_eq!(
            classify_runtime_value(RuntimeValue::from_int(7), TransferDomain::Device),
            RuntimeTransferClass::UnsupportedBoundary
        );
    }

    #[test]
    fn encoded_leaf_copy_matches_golden_vector() {
        let copy = RuntimeEncodedCopy {
            envelope: RuntimeTransferEnvelopeV1 {
                region_id: 7,
                generation: 2,
                source_domain: TransferDomain::Parent,
                target_domain: TransferDomain::Process,
                mode: TransferMode::Copy,
                payload: TransferPayload::EncodedCopy,
                ownership_token: 0,
                source_invalidated: false,
            },
            kind: EncodedLeafKind::Utf8,
            payload: b"typed".to_vec(),
        };
        assert_eq!(
            copy.encode().unwrap(),
            [
                0x53, 0x50, 0x54, 0x52, 0x01, 0x00, 0x00, 0x00, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0x00, 0x03, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x12, 0x10, 0x9a, 0x9b, 0xda, 0x7b, 0x41, 0x33,
                0x74, 0x79, 0x70, 0x65, 0x64,
            ]
        );
    }

    #[test]
    fn encoded_leaf_values_materialize_without_pointer_identity() {
        let values = [
            RuntimeValue::from_float(0.1),
            RuntimeValue::from_u64(u64::MAX),
            rt_string_new(b"independent".as_ptr(), 11),
        ];
        for source in values {
            let copy = RuntimeEncodedCopy::from_value(source, TransferDomain::Parent, TransferDomain::Thread).unwrap();
            let encoded = copy.encode().unwrap();
            let decoded = RuntimeEncodedCopy::decode_for_target(&encoded, TransferDomain::Thread).unwrap();
            let destination = decoded.materialize().unwrap();
            assert_ne!(source.to_raw(), destination.to_raw());
            if source.is_float() {
                assert_eq!(source.as_float().to_bits(), destination.as_float().to_bits());
            } else if let Some(value) = source.as_heap_u64() {
                assert_eq!(destination.as_heap_u64(), Some(value));
            } else {
                let destination_copy = RuntimeEncodedCopy::from_value(
                    destination,
                    TransferDomain::Thread,
                    TransferDomain::Parent,
                )
                .unwrap();
                assert_eq!(copy.payload, destination_copy.payload);
                assert_eq!(rt_string_free(source), 1);
                assert_eq!(rt_string_free(destination), 1);
            }
        }
    }

    #[test]
    fn encoded_leaf_copy_rejects_graphs_forgery_and_malformed_wire() {
        let array = rt_array_new(1);
        assert!(RuntimeEncodedCopy::from_value(array, TransferDomain::Parent, TransferDomain::Thread).is_none());
        assert!(RuntimeEncodedCopy::from_value(
            RuntimeValue::from_raw(0x1001),
            TransferDomain::Parent,
            TransferDomain::Thread,
        )
        .is_none());
        rt_array_free(array);

        let source = rt_string_new(b"valid".as_ptr(), 5);
        assert!(RuntimeEncodedCopy::from_value(source, TransferDomain::Parent, TransferDomain::Device).is_none());
        assert!(RuntimeEncodedCopy::from_value(source, TransferDomain::Parent, TransferDomain::Remote).is_none());
        let encoded = RuntimeEncodedCopy::from_value(source, TransferDomain::Parent, TransferDomain::Actor)
            .unwrap()
            .encode()
            .unwrap();
        assert!(RuntimeEncodedCopy::decode_for_target(&encoded, TransferDomain::Thread).is_none());

        for index in [40usize, 41, 56, encoded.len() - 1] {
            let mut malformed = encoded.clone();
            malformed[index] ^= 0xff;
            assert!(RuntimeEncodedCopy::decode_for_target(&malformed, TransferDomain::Actor).is_none());
        }
        assert!(RuntimeEncodedCopy::decode_for_target(&encoded[..encoded.len() - 1], TransferDomain::Actor).is_none());
        let mut trailing = encoded.clone();
        trailing.push(0);
        assert!(RuntimeEncodedCopy::decode_for_target(&trailing, TransferDomain::Actor).is_none());
        let mut oversize = encoded.clone();
        oversize[48..56].copy_from_slice(&((MAX_ENCODED_COPY_BYTES as u64) + 1).to_le_bytes());
        assert!(RuntimeEncodedCopy::decode_for_target(&oversize, TransferDomain::Actor).is_none());
        let invalid_utf8 = RuntimeEncodedCopy {
            envelope: RuntimeTransferEnvelopeV1::encoded_copy(
                TransferDomain::Parent,
                TransferDomain::Actor,
            )
            .unwrap(),
            kind: EncodedLeafKind::Utf8,
            payload: vec![0xff],
        };
        assert!(invalid_utf8.encode().is_none());
        let oversized = RuntimeEncodedCopy {
            envelope: invalid_utf8.envelope,
            kind: EncodedLeafKind::Utf8,
            payload: vec![b'a'; MAX_ENCODED_COPY_BYTES + 1],
        };
        assert!(oversized.encode().is_none());
        assert_eq!(rt_string_free(source), 1);
    }
}
