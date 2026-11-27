; XRay PR4 end-to-end targets. Attributes are exactly what PR3's
; llvm_xray_function_attrs emits (core_codegen.spl): "xray-always" for a
; sled function, "xray-never" for a never-listed one in an instrumented module.
; No target triple: the check script passes --target for x86_64 and aarch64.

define i64 @xray_target_a(i64 %x) #0 {
  %r = add i64 %x, 1
  ret i64 %r
}

define i64 @xray_target_b(i64 %x) #0 {
  %r = mul i64 %x, 3
  ret i64 %r
}

; ABI-01: eight integer and eight FP argument registers live across the entry
; sled; the FP return register lives across the exit sled.
define double @xray_abi_mix(i64 %a0, i64 %a1, i64 %a2, i64 %a3, i64 %a4, i64 %a5, i64 %a6, i64 %a7,
                            double %d0, double %d1, double %d2, double %d3,
                            double %d4, double %d5, double %d6, double %d7) #0 {
  %s1 = mul i64 %a1, 2
  %s2 = mul i64 %a2, 3
  %s3 = mul i64 %a3, 5
  %s4 = mul i64 %a4, 7
  %s5 = mul i64 %a5, 11
  %s6 = mul i64 %a6, 13
  %s7 = mul i64 %a7, 17
  %i1 = add i64 %a0, %s1
  %i2 = add i64 %i1, %s2
  %i3 = add i64 %i2, %s3
  %i4 = add i64 %i3, %s4
  %i5 = add i64 %i4, %s5
  %i6 = add i64 %i5, %s6
  %i7 = add i64 %i6, %s7
  %fi = sitofp i64 %i7 to double
  %f1 = fmul double %d1, 2.0
  %f2 = fmul double %d2, 4.0
  %f3 = fmul double %d3, 8.0
  %f4 = fmul double %d4, 16.0
  %f5 = fmul double %d5, 32.0
  %f6 = fmul double %d6, 64.0
  %f7 = fmul double %d7, 128.0
  %g1 = fadd double %d0, %f1
  %g2 = fadd double %g1, %f2
  %g3 = fadd double %g2, %f3
  %g4 = fadd double %g3, %f4
  %g5 = fadd double %g4, %f5
  %g6 = fadd double %g5, %f6
  %g7 = fadd double %g6, %f7
  %r = fadd double %g7, %fi
  ret double %r
}

; ABI-01: indirect (sret) aggregate result pointer live across the entry sled.
%quad = type { i64, i64, i64, i64 }
define void @xray_abi_sret(ptr sret(%quad) %out, i64 %x) #0 {
  %p0 = getelementptr inbounds %quad, ptr %out, i32 0, i32 0
  %p1 = getelementptr inbounds %quad, ptr %out, i32 0, i32 1
  %p2 = getelementptr inbounds %quad, ptr %out, i32 0, i32 2
  %p3 = getelementptr inbounds %quad, ptr %out, i32 0, i32 3
  store i64 %x, ptr %p0
  %x1 = add i64 %x, 1
  store i64 %x1, ptr %p1
  %x2 = add i64 %x, 2
  store i64 %x2, ptr %p2
  %x3 = add i64 %x, 3
  store i64 %x3, ptr %p3
  ret void
}

; Never-listed: must get no sled and no function id.
define i64 @xray_never_fn(i64 %x) #1 {
  %r = sub i64 %x, 1
  ret i64 %r
}

attributes #0 = { noinline nounwind "function-instrument"="xray-always" }
attributes #1 = { noinline nounwind "function-instrument"="xray-never" }
