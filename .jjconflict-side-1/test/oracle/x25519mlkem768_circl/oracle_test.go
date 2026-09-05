package x25519mlkem768circl

import (
	"bytes"
	"encoding/hex"
	"os"
	"strings"
	"testing"

	"github.com/cloudflare/circl/kem/mlkem/mlkem768"
)

const vectorPath = "../../fixtures/crypto/x25519mlkem768/mlkem_native_fd58_vectors.sdn"

func field(t *testing.T, text, name string) []byte {
	t.Helper()
	prefix := "  " + name + ": \""
	for _, line := range strings.Split(text, "\n") {
		if strings.HasPrefix(line, prefix) && strings.HasSuffix(line, "\"") {
			value, err := hex.DecodeString(strings.TrimSuffix(strings.TrimPrefix(line, prefix), "\""))
			if err != nil { t.Fatalf("%s is not hexadecimal: %v", name, err) }
			return value
		}
	}
	t.Fatalf("missing %s", name)
	return nil
}

func equal(t *testing.T, name string, got, want []byte) {
	t.Helper()
	if !bytes.Equal(got, want) { t.Fatalf("%s differs: got %d bytes, want %d", name, len(got), len(want)) }
}

func TestMlKem768Fd58Vector(t *testing.T) {
	raw, err := os.ReadFile(vectorPath)
	if err != nil { t.Fatalf("read pinned vector: %v", err) }
	text := string(raw)
	d, z := field(t, text, "d_hex"), field(t, text, "z_hex")
	seed := append(append([]byte{}, d...), z...)
	pk, sk := mlkem768.NewKeyFromSeed(seed)
	ek := make([]byte, mlkem768.PublicKeySize)
	dk := make([]byte, mlkem768.PrivateKeySize)
	pk.Pack(ek)
	sk.Pack(dk)
	equal(t, "encapsulation key", ek, field(t, text, "encapsulation_key_hex"))
	equal(t, "decapsulation key", dk, field(t, text, "decapsulation_key_hex"))
	ct, ss := make([]byte, mlkem768.CiphertextSize), make([]byte, mlkem768.SharedKeySize)
	pk.EncapsulateTo(ct, ss, field(t, text, "m_hex"))
	equal(t, "ciphertext", ct, field(t, text, "ciphertext_hex"))
	equal(t, "shared secret", ss, field(t, text, "shared_secret_hex"))
	decapsulated := make([]byte, mlkem768.SharedKeySize)
	sk.DecapsulateTo(decapsulated, ct)
	equal(t, "decapsulated shared secret", decapsulated, ss)
}
