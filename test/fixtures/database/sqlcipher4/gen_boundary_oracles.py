"""Independent SQLCipher4 boundary oracle; never imports Simple production code.
Prints SDN, does not rewrite specs or mint execution evidence.
PBKDF2 RFC 8018 section 5.2; SQLCipher format: salt XOR 0x3a, fast KDF=2.
"""
import hashlib
import hmac
import platform
import ssl
password = bytes([0,127,128,255,0,65])
salt = bytes(range(16))
page_key = hashlib.pbkdf2_hmac("sha512", password, salt, 256000, 32)
mac_key = hashlib.pbkdf2_hmac("sha512", page_key, bytes(x ^ 0x3a for x in salt), 2, 32)
print('schema: "sqlcipher4-boundary-oracles/1"')
print('proof_class: "independent-python-oracle-only"')
print('python: "' + platform.python_version() + '"')
print('provider: "' + ssl.OPENSSL_VERSION + '"')
print('password_hex: "' + password.hex() + '"')
print('salt_hex: "' + salt.hex() + '"')
print('page_key_hex: "' + page_key.hex() + '"')
print('hmac_key_hex: "' + mac_key.hex() + '"')
for n in [255,256,65536,2147483648,4294967295]:
    payload = bytes([0,127,128,255]) + bytes(range(16)) + n.to_bytes(4,"little")
    digest = hmac.new(bytes(range(32)), payload, hashlib.sha512).hexdigest()
    print('page_' + str(n) + '_hmac: "' + digest + '"')
