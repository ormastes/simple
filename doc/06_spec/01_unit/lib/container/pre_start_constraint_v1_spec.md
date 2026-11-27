# Restrictive pre-start comparison

Status: AUTHORED_NOT_RUN, DATA-only. No actual creation/admission is fabricated.

The production comparison accepts an exact matching configuration DATA projection,
then rejects changed image, argv, environment, workdir, user, mounts, read-only
root, native ID and provider generation. The production defensive-copy function
keeps retained argv and nested mount fields unchanged after caller mutation.
Positive DATA equality is not a native first-start receipt.
