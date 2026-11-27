target triple = "aarch64-unknown-linux-gnu"
@sink = global i32 0
define i32 @live() noinline !pcsections !{!"simple_xray_semantic_v1", !{i64 3552587323878299731, i32 1, i32 56, i32 8, i32 5, i64 0, i8 112, i8 114, i8 111, i8 98, i8 101, i8 46, i8 102, i8 49, i8 112, i8 114, i8 111, i8 98, i8 101, i8 0, i8 0, i8 0}} {
  store volatile i32 7, ptr @sink
  ret i32 7
}
define i32 @dead_link() noinline !pcsections !1 {
  ret i32 8
}
define internal i32 @dead_ir() noinline !pcsections !2 {
  ret i32 9
}
define i32 @main() {
  %r = call i32 @live()
  ret i32 %r
}
!0 = !{!"simple_xray_semantic_v1", !3}
!1 = !{!"simple_xray_semantic_v1", !4}
!2 = !{!"simple_xray_semantic_v1", !5}
!3 = !{i64 3552587323878299731, i32 1, i32 56, i32 8, i32 5, i64 0, i8 112, i8 114, i8 111, i8 98, i8 101, i8 46, i8 102, i8 49, i8 112, i8 114, i8 111, i8 98, i8 101, i8 0, i8 0, i8 0}
!4 = !{i64 3552587323878299731, i32 1, i32 56, i32 8, i32 5, i64 0, i8 112, i8 114, i8 111, i8 98, i8 101, i8 46, i8 102, i8 50, i8 112, i8 114, i8 111, i8 98, i8 101, i8 0, i8 0, i8 0}
!5 = !{i64 3552587323878299731, i32 1, i32 56, i32 8, i32 5, i64 0, i8 112, i8 114, i8 111, i8 98, i8 101, i8 46, i8 102, i8 51, i8 112, i8 114, i8 111, i8 98, i8 101, i8 0, i8 0, i8 0}
