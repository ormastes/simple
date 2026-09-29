# SimpleOS ARM64 VirtIO-Net QEMU Verification

TODO: Once the admitted phase compiler and ARM64 SimpleOS QEMU environment are
ready, run the ARM64 guest network scenario and verify at least nine sequential
TX submissions, a deliberately delayed completion, descriptor reuse without
`EAGAIN`, and unchanged bounded queue memory. Record the guest serial transcript
and QEMU exit status in the SimpleOS bootstrap evidence bundle.
