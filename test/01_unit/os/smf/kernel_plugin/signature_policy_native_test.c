#include <stdbool.h>
#include <stdio.h>
#include <string.h>

typedef struct {
    const char *artifact_digest;
    const char *publisher;
    const char *key;
    const char *scheme;
    const char *signature_digest;
    bool publisher_revoked;
    bool key_revoked;
} policy_v1;

typedef struct {
    const char *artifact_digest;
    const char *publisher;
    const char *key;
    const char *scheme;
    const char *signature_digest;
    bool signature_present;
    bool signature_verified;
} evidence_v1;

static bool admit(const policy_v1 *policy, const evidence_v1 *evidence) {
    return strlen(policy->artifact_digest) == 64 &&
           strcmp(policy->artifact_digest, evidence->artifact_digest) == 0 &&
           policy->publisher[0] != '\0' &&
           strcmp(policy->publisher, evidence->publisher) == 0 &&
           !policy->publisher_revoked && policy->key[0] != '\0' &&
           strcmp(policy->key, evidence->key) == 0 && !policy->key_revoked &&
           policy->scheme[0] != '\0' &&
           strcmp(policy->scheme, evidence->scheme) == 0 &&
           strlen(policy->signature_digest) == 64 &&
           evidence->signature_present &&
           strcmp(policy->signature_digest, evidence->signature_digest) == 0 &&
#ifndef KPF_MUTATE_SKIP_VERIFICATION
           evidence->signature_verified;
#else
           true;
#endif
}

int main(void) {
    const char *artifact = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    const char *signature = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
    policy_v1 policy = {artifact, "simple.project", "release-2026", "ed25519", signature, false, false};
    evidence_v1 evidence = {artifact, "simple.project", "release-2026", "ed25519", signature, true, true};
    if (!admit(&policy, &evidence)) return 10;
    evidence.signature_present = false;
    if (admit(&policy, &evidence)) return 11;
    evidence.signature_present = true;
    evidence.signature_verified = false;
    if (admit(&policy, &evidence)) return 12;
    evidence.signature_verified = true;
    policy.publisher_revoked = true;
    if (admit(&policy, &evidence)) return 13;
    policy.publisher_revoked = false;
    evidence.artifact_digest = signature;
    if (admit(&policy, &evidence)) return 14;
    puts("KPF_SIGNATURE_TRUST_NATIVE: PASS");
    return 0;
}
