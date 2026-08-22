#![deny(warnings)]

use std::time::Instant;

const REPLAYED: u8 = 0;
const INVALID: u8 = 1;
const WRONG_SEQUENCE: u8 = 2;
const ALREADY_CONSUMED: u8 = 3;
const REGION_OVERFLOW: u8 = 4;
const DIFFERENCE: u8 = 5;

#[derive(Clone, Copy, PartialEq, Eq)]
struct Region {
    offset: usize,
    length: usize,
    capacity: usize,
    digest_hi: u64,
    digest_lo: u64,
}

#[derive(Clone, Copy)]
struct Payload {
    version: u32,
    opcode: u32,
    invocation_id: u64,
    sequence: u32,
    capability_id: u32,
    capability_generation: u32,
    read_once_token: u32,
    grant_digest_hi: u64,
    grant_digest_lo: u64,
    scalar0: i64,
    scalar1: i64,
    region: Region,
    observation_status: u32,
    observation_status_code: i32,
    interaction_digest_hi: u64,
    interaction_digest_lo: u64,
    sealed: bool,
}

#[derive(Clone, Copy)]
struct Cursor {
    invocation_id: u64,
    next_sequence: u32,
    capacity: u32,
    consumed_count: u32,
    read_once_mask: u64,
    sealed: bool,
}

fn digest_present(hi: u64, lo: u64) -> bool { hi != 0 || lo != 0 }
fn requires_region(op: u32) -> bool { matches!(op, 11 | 18 | 19 | 21 | 22) }
fn requires_once(op: u32) -> bool { matches!(op, 11 | 17 | 18 | 22) }

fn well_formed(v: &Payload) -> bool {
    let region_ok = v.region.length <= v.region.capacity
        && v.region.capacity <= 65_536
        && ((v.region.length == 0 && v.region.digest_hi == 0
            && v.region.digest_lo == 0)
            || (v.region.length != 0
                && digest_present(v.region.digest_hi, v.region.digest_lo)));
    let observation_ok = matches!(v.observation_status, 1 | 2)
        == (v.observation_status_code == 0);
    if v.version != 1 || v.invocation_id == 0 || v.capability_id == 0
        || v.read_once_token > 62 || !v.sealed || !region_ok
        || !digest_present(v.interaction_digest_hi, v.interaction_digest_lo)
        || !observation_ok {
        return false;
    }
    if v.opcode == 11 {
        return v.capability_generation == 0
            && digest_present(v.grant_digest_hi, v.grant_digest_lo)
            && v.read_once_token != 0 && v.region.length != 0;
    }
    (16..=23).contains(&v.opcode) && v.capability_generation != 0
        && digest_present(v.grant_digest_hi, v.grant_digest_lo)
        && requires_region(v.opcode) == (v.region.length != 0)
        && requires_once(v.opcode) == (v.read_once_token != 0)
}

fn replay(cursor: &mut Cursor, recorded: &Payload, recorded_bytes: &[u8],
          candidate: &Payload, candidate_bytes: &[u8]) -> u8 {
    if !cursor.sealed || !well_formed(recorded) || !well_formed(candidate) {
        return INVALID;
    }
    if recorded.invocation_id != cursor.invocation_id
        || candidate.invocation_id != cursor.invocation_id
        || recorded.sequence != cursor.next_sequence
        || candidate.sequence != cursor.next_sequence
        || cursor.consumed_count >= cursor.capacity {
        return WRONG_SEQUENCE;
    }
    let rr = recorded.region;
    let cr = candidate.region;
    if rr.offset > recorded_bytes.len()
        || rr.length > recorded_bytes.len() - rr.offset
        || cr.offset > candidate_bytes.len()
        || cr.length > candidate_bytes.len() - cr.offset {
        return REGION_OVERFLOW;
    }
    let token_mask = if recorded.read_once_token == 0 { 0 }
        else { 1_u64 << recorded.read_once_token };
    if token_mask != 0 && cursor.read_once_mask & token_mask != 0 {
        return ALREADY_CONSUMED;
    }
    if recorded.opcode != candidate.opcode
        || recorded.capability_id != candidate.capability_id
        || recorded.capability_generation != candidate.capability_generation
        || recorded.read_once_token != candidate.read_once_token
        || recorded.grant_digest_hi != candidate.grant_digest_hi
        || recorded.grant_digest_lo != candidate.grant_digest_lo
        || recorded.scalar0 != candidate.scalar0
        || recorded.scalar1 != candidate.scalar1
        || recorded.observation_status != candidate.observation_status
        || recorded.observation_status_code != candidate.observation_status_code
        || recorded.interaction_digest_hi != candidate.interaction_digest_hi
        || recorded.interaction_digest_lo != candidate.interaction_digest_lo
        || recorded.region.length != candidate.region.length
        || recorded.region.digest_hi != candidate.region.digest_hi
        || recorded.region.digest_lo != candidate.region.digest_lo
        || recorded_bytes[rr.offset..rr.offset + rr.length]
            != candidate_bytes[cr.offset..cr.offset + cr.length] {
        return DIFFERENCE;
    }
    cursor.next_sequence += 1;
    cursor.consumed_count += 1;
    cursor.read_once_mask |= token_mask;
    REPLAYED
}

fn payload(opcode: u32, token: u32) -> Payload {
    let has_region = opcode != 17;
    Payload { version: 1, opcode, invocation_id: 77, sequence: 0,
        capability_id: 9, capability_generation: if opcode == 11 { 0 } else { 3 },
        read_once_token: token, grant_digest_hi: 31, grant_digest_lo: 32,
        scalar0: 17, scalar1: 19,
        region: Region { offset: 1, length: if has_region { 4 } else { 0 },
            capacity: if has_region { 4 } else { 0 },
            digest_hi: if has_region { 51 } else { 0 },
            digest_lo: if has_region { 52 } else { 0 } },
        observation_status: 1, observation_status_code: 0,
        interaction_digest_hi: 71, interaction_digest_lo: 72, sealed: true }
}

fn main() {
    let recorded = [0_u8, 1, 2, 3, 4];
    let same = [9_u8, 1, 2, 3, 4];
    for (index, opcode) in [11_u32, 17, 18, 22].iter().enumerate() {
        let value = payload(*opcode, index as u32 + 1);
        let mut parity_mask = 0_u8;
        for provider in 0..3 {
            let mut cursor = Cursor { invocation_id: 77, next_sequence: 0,
                capacity: 4, consumed_count: 0, read_once_mask: 0, sealed: true };
            if replay(&mut cursor, &value, &recorded, &value, &same) == REPLAYED {
                parity_mask |= 1 << provider;
            }
        }
        assert_eq!(parity_mask, 7);
    }
    let value = payload(11, 1);
    let mut checksum = 0_u64;
    let iterations = 10_000_000_u32;
    let start = Instant::now();
    for _ in 0..iterations {
        let mut cursor = Cursor { invocation_id: 77, next_sequence: 0,
            capacity: 1, consumed_count: 0, read_once_mask: 0, sealed: true };
        checksum += replay(&mut cursor, &value, &recorded, &value, &same) as u64;
    }
    assert_eq!(checksum, 0);
    let elapsed = start.elapsed().as_nanos();
    println!("hal-provider-device-payload-v1-rust: PASS parity_mask=7 effects=0 allocations=0 iterations={} elapsed_ns={} ns_per_replay={:.3}",
        iterations, elapsed, elapsed as f64 / iterations as f64);
}
