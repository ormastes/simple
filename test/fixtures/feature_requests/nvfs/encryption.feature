# Feature: NVFS real AES-GCM encryption
# Anchors: N6a-001 (encrypt-on-write), N6a-002 (decrypt-on-read), N6a-003 (key rotation)
# Target: src/lib/nogc_sync_mut/fs/nvfs/crypto.spl, nvfs/api.spl
# Status: pending — wave 7 impl must satisfy these contracts.

Feature: NVFS AES-128-GCM encryption for arena data
  As a storage security engineer
  I want arena writes to be encrypted with AES-128-GCM and reads transparently decrypted
  So that data at rest is protected per N6a requirements

  Background:
    Given an NVFS instance initialized with StorageClass = Encrypted
    And   a 128-bit AES-GCM key K registered via "nvfs_key_register(key_id: 1, key: K)"

  Scenario: Golden path — encrypt on write, decrypt on read (N6a-001 / N6a-002)
    Given an arena A created with class Encrypted and key_id 1
    When  I append plaintext "hello world" to arena A with Durability = DURABLE_GROUP_COMMIT
    Then  the on-disk bytes at the returned Offset are NOT equal to "hello world"
    And   arena_read of that Offset returns exactly "hello world"
    And   the GCM tag appended after the ciphertext verifies without error

  Scenario: Wrong key returns DecryptFailed (N6a-002 edge case)
    Given an arena A created with class Encrypted and key_id 1
    And   a ciphertext block written under key_id 1
    When  I register a different key as key_id 1 and call arena_read on that block
    Then  arena_read returns Err(FsErr::DecryptFailed)
    And   no plaintext bytes are exposed to the caller

  Scenario: Nonce uniqueness — two appends produce distinct ciphertexts
    Given an arena A created with class Encrypted and key_id 1
    When  I append the same 16-byte plaintext "AAAAAAAAAAAAAAAA" twice to arena A
    Then  the two resulting ciphertext blocks at their respective Offsets differ
    And   both blocks decrypt successfully to "AAAAAAAAAAAAAAAA"

  Scenario: Key rotation re-encrypts existing sealed arena (N6a-003)
    Given a sealed arena A whose blocks were encrypted under key_id 1
    When  I call "nvfs_key_rotate(arena: A, old_key_id: 1, new_key_id: 2)"
    Then  the operation completes with Ok(())
    And   arena_read of any block in A now succeeds using key_id 2
    And   arena_read with key_id 1 returns Err(FsErr::DecryptFailed)

  Scenario: Unencrypted arena rejects key_id parameter
    Given an arena B created with class Standard (no encryption)
    When  I attempt to register a key_id against arena B
    Then  the call returns Err(FsErr::CapabilityMismatch)
    And   subsequent arena_append and arena_read on B proceed without encryption overhead
