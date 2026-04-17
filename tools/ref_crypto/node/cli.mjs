#!/usr/bin/env node
// Reference crypto CLI — Node.js node:crypto.
// Invoked by test/support/crypto_ref_harness.spl via rt_process_run.
// Uniform argv contract: <prim> <hex_args...>. Stdout: lowercase hex. Exit 0 on success.

import * as crypto from "node:crypto";
import { Buffer } from "node:buffer";

const err = (m) => { process.stderr.write(`ref_node: ${m}\n`); process.exit(2); };
const hx = (s) => Buffer.from(s || "", "hex");
const out = (b) => process.stdout.write(Buffer.from(b).toString("hex") + "\n");

const [, , prim, ...a] = process.argv;
if (!prim) err("usage: cli.mjs <primitive> <args...>");

try {
  switch (prim) {
    case "sha256":
      out(crypto.createHash("sha256").update(hx(a[0])).digest()); break;
    case "sha512":
      out(crypto.createHash("sha512").update(hx(a[0])).digest()); break;
    case "hmac_sha256":
      out(crypto.createHmac("sha256", hx(a[0])).update(hx(a[1])).digest()); break;
    case "hmac_sha512":
      out(crypto.createHmac("sha512", hx(a[0])).update(hx(a[1])).digest()); break;
    case "hkdf_sha256": {
      const [salt, ikm, info, length] = [hx(a[0]), hx(a[1]), hx(a[2]), parseInt(a[3], 10)];
      const k = crypto.hkdfSync("sha256", ikm, salt, info, length);
      out(Buffer.from(k)); break;
    }
    case "pbkdf2_sha256": {
      const [pw, salt, iters, length] = [hx(a[0]), hx(a[1]), parseInt(a[2], 10), parseInt(a[3], 10)];
      out(crypto.pbkdf2Sync(pw, salt, iters, length, "sha256")); break;
    }
    case "aes_128_gcm_encrypt":
    case "aes_256_gcm_encrypt": {
      const [key, nonce, aad, plain] = [hx(a[0]), hx(a[1]), hx(a[2]), hx(a[3])];
      const algo = prim === "aes_128_gcm_encrypt" ? "aes-128-gcm" : "aes-256-gcm";
      const c = crypto.createCipheriv(algo, key, nonce);
      if (aad.length) c.setAAD(aad);
      const ct = Buffer.concat([c.update(plain), c.final()]);
      const tag = c.getAuthTag();
      out(Buffer.concat([ct, tag])); break;
    }
    case "chacha20_poly1305_encrypt": {
      const [key, nonce, aad, plain] = [hx(a[0]), hx(a[1]), hx(a[2]), hx(a[3])];
      const c = crypto.createCipheriv("chacha20-poly1305", key, nonce, { authTagLength: 16 });
      if (aad.length) c.setAAD(aad);
      const ct = Buffer.concat([c.update(plain), c.final()]);
      const tag = c.getAuthTag();
      out(Buffer.concat([ct, tag])); break;
    }
    case "x25519": {
      // Node needs DER-wrapped raw keys. Construct SPKI/PKCS8 wrappers.
      const scalar = hx(a[0]); const peer = hx(a[1]);
      // PKCS#8 X25519 private key prefix (raw 32-byte scalar at end)
      const pkcs8Prefix = Buffer.from("302e020100300506032b656e04220420", "hex");
      const spkiPrefix = Buffer.from("302a300506032b656e032100", "hex");
      const sk = crypto.createPrivateKey({
        key: Buffer.concat([pkcs8Prefix, scalar]), format: "der", type: "pkcs8"
      });
      const pk = crypto.createPublicKey({
        key: Buffer.concat([spkiPrefix, peer]), format: "der", type: "spki"
      });
      out(crypto.diffieHellman({ privateKey: sk, publicKey: pk })); break;
    }
    case "ed25519_sign": {
      const sk = hx(a[0]); const msg = hx(a[1]);
      const pkcs8Prefix = Buffer.from("302e020100300506032b657004220420", "hex");
      const key = crypto.createPrivateKey({
        key: Buffer.concat([pkcs8Prefix, sk]), format: "der", type: "pkcs8"
      });
      out(crypto.sign(null, msg, key)); break;
    }
    case "ed25519_verify": {
      const pk = hx(a[0]); const msg = hx(a[1]); const sig = hx(a[2]);
      const spkiPrefix = Buffer.from("302a300506032b6570032100", "hex");
      const key = crypto.createPublicKey({
        key: Buffer.concat([spkiPrefix, pk]), format: "der", type: "spki"
      });
      process.stdout.write((crypto.verify(null, msg, key, sig) ? "1" : "0") + "\n");
      break;
    }
    default:
      err(`unsupported primitive: ${prim}`);
  }
} catch (e) {
  err(e.message || String(e));
}
