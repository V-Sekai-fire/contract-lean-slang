import LeanSlang.Types
import LeanSlang.AST
import LeanSlang.Emit

open LeanSlang

/-! ## Exact float literal fixtures pinned by `native_decide`

`litFloat` prints six decimal places (Lean's `Float.toString`), so a
guard such as `1e-12` emits as `0.000000` and never fires. The
additive `litFloatExact` / `litDoubleExact` forms print the shortest
decimal that parses back to the same binary32 / binary64. Every value
below, and 3000 random ones, was emitted into one kernel, compiled
with `slangc -target spirv` (constants read back from the SPIR-V) and
`slangc -target cpp` (run on the host), and matched bit for bit on
both targets.
-/

/-! ### `litFloat` is unchanged: the defect these forms exist for -/

example : emitExpr (.litFloat 1e-12) = "0.000000" := by native_decide
example : emitExpr (.litFloat 1e-9) = "0.000000" := by native_decide
example : emitExpr (.litFloat (1.0 / 3.0)) = "0.333333" := by native_decide

/-! ### binary32 -/

example : emitExpr (.litFloatExact 1e-12) = "1.0e-12f" := by native_decide
example : emitExpr (.litFloatExact 1e-9) = "1.0e-9f" := by native_decide
example : emitExpr (.litFloatExact 0.1) = "0.1f" := by native_decide
example : emitExpr (.litFloatExact (1.0 / 3.0)) = "0.33333334f" := by native_decide
example : emitExpr (.litFloatExact (2.0 / 3.0)) = "0.6666667f" := by native_decide
example : emitExpr (.litFloatExact 0.0) = "0.0f" := by native_decide
example : emitExpr (.litFloatExact (-0.0)) = "(-0.0f)" := by native_decide
example : emitExpr (.litFloatExact (-2.5)) = "(-2.5f)" := by native_decide
example : emitExpr (.litFloatExact 1.0) = "1.0f" := by native_decide
example : emitExpr (.litFloatExact 1e-5) = "0.00001f" := by native_decide
example : emitExpr (.litFloatExact 3.14159265358979323846) = "3.1415927f" := by
  native_decide
/-- FLT_MIN, the smallest normal binary32. -/
example : emitExpr (.litFloatExact 1.17549435082228750797e-38) = "1.1754944e-38f" := by
  native_decide
/-- The smallest binary32 subnormal, 2^-149. -/
example : emitExpr (.litFloatExact 1.401298464324817e-45) = "1.0e-45f" := by
  native_decide
/-- FLT_MAX. -/
example : emitExpr (.litFloatExact 3.4028234663852886e38) = "3.4028235e38f" := by
  native_decide
example : emitExpr (.litFloatExact 1e30) = "1.0e30f" := by native_decide
/-- Rounded to binary32 first: 2^24 + 1 is not representable. -/
example : emitExpr (.litFloatExact 16777217.0) = "16777216.0f" := by native_decide
example : emitExpr (.litFloatExact 123456789.0) = "123456790.0f" := by native_decide
/-- Finite as binary64, infinite as binary32: the bit pattern. -/
example : emitExpr (.litFloatExact 1e39) = "asfloat(0x7F800000u)" := by native_decide
example : emitExpr (.litFloatExact (-1.0 / 0.0)) = "asfloat(0xFF800000u)" := by
  native_decide
example : emitExpr (.litFloatExact (Float.ofBits 0x7FF8000000000000))
    = "asfloat(0x7FC00000u)" := by
  native_decide

/-! ### binary64 -/

example : emitExpr (.litDoubleExact 1e-12) = "1.0e-12L" := by native_decide
example : emitExpr (.litDoubleExact 1e-9) = "1.0e-9L" := by native_decide
example : emitExpr (.litDoubleExact 0.1) = "0.1L" := by native_decide
example : emitExpr (.litDoubleExact (1.0 / 3.0)) = "0.3333333333333333L" := by
  native_decide
example : emitExpr (.litDoubleExact (2.0 / 3.0)) = "0.6666666666666666L" := by
  native_decide
example : emitExpr (.litDoubleExact (-0.0)) = "(-0.0L)" := by native_decide
example : emitExpr (.litDoubleExact 3.14159265358979323846) = "3.141592653589793L" := by
  native_decide
/-- DBL_MIN, the smallest normal binary64. -/
example : emitExpr (.litDoubleExact 2.2250738585072014e-308)
    = "2.2250738585072014e-308L" := by
  native_decide
/-- The smallest binary64 subnormal, 2^-1074. -/
example : emitExpr (.litDoubleExact 5e-324) = "5.0e-324L" := by native_decide
/-- DBL_MAX. -/
example : emitExpr (.litDoubleExact 1.7976931348623157e308)
    = "1.7976931348623157e308L" := by
  native_decide
example : emitExpr (.litDoubleExact 1e20) = "1.0e20L" := by native_decide
example : emitExpr (.litDoubleExact 16777217.0) = "16777217.0L" := by native_decide
/-- slangc -target cpp would re-print this as `0.00007075852045091`
    (fixed, 17 places), 97 ulps off, so it goes out as its bits. -/
example : emitExpr (.litDoubleExact 7.075852045090869e-5)
    = "asdouble(0x20000000u, 0x3F128C86u)" := by
  native_decide
/-- The same magnitude with a short decimal survives the fixed form. -/
example : emitExpr (.litDoubleExact 7.5e-5) = "0.000075L" := by native_decide
example : emitExpr (.litDoubleExact (1.0 / 0.0)) = "asdouble(0x00000000u, 0x7FF00000u)" := by
  native_decide

/-! ### In context -/

example : emitExpr (.bin "*" (.var "x") (.litFloatExact (-0.5))) = "(x * (-0.5f))" := by
  native_decide

/-- A degenerate-length guard of the kind the curve kernels carry. -/
def exactGuardShader : SlangShaderModule :=
  { globals :=
      [ ⟨"len", .rwBuf (.scalar .float),  Semantic.none, some 0, some 0, .qIn⟩
      , ⟨"acc", .rwBuf (.scalar .double), Semantic.none, some 1, some 0, .qIn⟩ ]
    functions := [{
      attrs  := [.shaderCompute, .numthreads 64 1 1]
      name   := "main"
      params := [⟨"tid", .vec .uint 3, .svDispatchThreadId, none, none, .qIn⟩]
      body   :=
        [ .declInit (.scalar .uint) "i" (.member (.var "tid") "x")
        , .ifNoElse (.bin "<" (.index (.var "len") (.var "i")) (.litFloatExact 1e-12))
            [ .assign (.index (.var "len") (.var "i")) (.litFloatExact 1e-12) ]
        , .assign (.index (.var "acc") (.var "i"))
            (.bin "*" (.index (.var "acc") (.var "i")) (.litDoubleExact (1.0 / 3.0))) ] }] }

example : emit exactGuardShader =
"[[vk::binding(0, 0)]]
RWStructuredBuffer<float> len;
[[vk::binding(1, 0)]]
RWStructuredBuffer<double> acc;

[shader(\"compute\")] [numthreads(64, 1, 1)]
void main(uint3 tid : SV_DispatchThreadID) {
  uint i = tid.x;
  if ((len[i] < 1.0e-12f)) {
    len[i] = 1.0e-12f;
  }
  acc[i] = (acc[i] * 0.3333333333333333L);
}" := by native_decide
