.option norelax
.option norvc
.text
.globl _start, ie_value, ie_second, ie_zero, ie_repeat
.type _start,@function
_start:
ie_value:
  auipc a0, %tls_ie_pcrel_hi(ie_tls_value)
  nop
  ld a0, %pcrel_lo(ie_value)(a0)
  add a0, a0, tp
ie_second:
  auipc a1, %tls_ie_pcrel_hi(ie_tls_second)
  ld a1, %pcrel_lo(ie_second)(a1)
ie_zero:
  auipc a2, %tls_ie_pcrel_hi(ie_tls_zero)
  ld a2, %pcrel_lo(ie_zero)(a2)
ie_repeat:
  auipc a3, %tls_ie_pcrel_hi(ie_tls_value)
  ld a3, %pcrel_lo(ie_repeat)(a3)
  ret
.size _start, .-_start
