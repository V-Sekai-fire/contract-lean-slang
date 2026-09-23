import LeanSlang.Types
import LeanSlang.AST
import LeanSlang.Emit

open LeanSlang

/-! ## Floating-point width fixtures pinned by `native_decide`

`half` / `double` scalars and the `litHalf`, `litInt` and `cast`
expressions. Every expected string below was also fed to `slangc`
(`-target spirv` and `-target cpp`) when these constructors landed,
so the text is known to compile, not only to match.
-/

/-! ### Types -/

example : emitSlangType (.scalar .half) = "half" := by native_decide
example : emitSlangType (.vec .half 4) = "half4" := by native_decide
example : emitSlangType (.mat .half 4 4) = "half4x4" := by native_decide
example : emitSlangType (.roBuf (.scalar .half)) = "StructuredBuffer<half>" := by
  native_decide
example : emitSlangType (.rwBuf (.vec .half 4)) = "RWStructuredBuffer<half4>" := by
  native_decide
example : emitSlangType (.scalar .double) = "double" := by native_decide
example : emitSlangType (.vec .double 3) = "double3" := by native_decide

/-! ### Literals and casts -/

example : emitExpr (.litHalf 1.5) = "1.500000h" := by native_decide
example : emitExpr (.litHalf (-0.25)) = "-0.250000h" := by native_decide
example : emitExpr (.litInt (-3)) = "(-3)" := by native_decide
example : emitExpr (.litInt 3) = "3" := by native_decide
example : emitExpr (.litInt 0) = "0" := by native_decide
example : emitExpr (.bin "+" (.var "a") (.litInt (-1))) = "(a + (-1))" := by
  native_decide
example : emitExpr (.cast (.scalar .float) (.index (.var "w") (.var "i")))
    = "float(w[i])" := by
  native_decide
example : emitExpr (.cast (.vec .half 4) (.var "v")) = "half4(v)" := by
  native_decide
example : emitExpr (.cast (.scalar .double) (.litInt (-3))) = "double((-3))" := by
  native_decide

/-- A `half4` local built from half literals. -/
example :
    emitStmt 0 (.declInit (.vec .half 4) "h"
      (.call "half4" [.litHalf 1.5, .litHalf (-0.25), .litHalf 0.0, .litHalf 1.0]))
    = "half4 h = half4(1.500000h, -0.250000h, 0.000000h, 1.000000h);" := by
  native_decide

/-! ### HalfLoad: f16 storage read, f32 arithmetic

The shape of an f16 weight read: the buffer holds `half`, the
arithmetic is `float`. slangc 2026.13 still declares `Float16` next to
`UniformAndStorageBuffer16BitAccess` for it (spirv-val vulkan1.3
clean), so a device needs both features. -/

def halfLoadShader : SlangShaderModule :=
  { globals :=
      [ ⟨"w", .roBuf (.scalar .half),  Semantic.none, some 0, some 0, .qIn⟩
      , ⟨"o", .rwBuf (.scalar .float), Semantic.none, some 1, some 0, .qIn⟩ ]
  , functions := [{
      attrs  := [.shaderCompute, .numthreads 64 1 1]
      name   := "main"
      params := [⟨"tid", .vec .uint 3, .svDispatchThreadId, none, none, .qIn⟩]
      body   :=
        [ .declInit (.scalar .uint) "i" (.member (.var "tid") "x")
        , .assign (.index (.var "o") (.var "i"))
            (.bin "*" (.cast (.scalar .float) (.index (.var "w") (.var "i")))
                      (.litFloat 2.0))
        , .ret none ]
    }] }

def halfLoadShaderExpected : String :=
"[[vk::binding(0, 0)]]
StructuredBuffer<half> w;
[[vk::binding(1, 0)]]
RWStructuredBuffer<float> o;

[shader(\"compute\")] [numthreads(64, 1, 1)]
void main(uint3 tid : SV_DispatchThreadID) {
  uint i = tid.x;
  o[i] = (float(w[i]) * 2.000000);
  return;
}"

example : LeanSlang.emit halfLoadShader = halfLoadShaderExpected := by
  native_decide

/-! ### HalfArith: arithmetic in half

A `half` product with a half literal before widening: `Float16`
arithmetic proper, beside the 16-bit storage access. -/

def halfArithShader : SlangShaderModule :=
  { globals :=
      [ ⟨"w", .roBuf (.scalar .half),  Semantic.none, some 0, some 0, .qIn⟩
      , ⟨"o", .rwBuf (.scalar .float), Semantic.none, some 1, some 0, .qIn⟩ ]
  , functions := [{
      attrs  := [.shaderCompute, .numthreads 64 1 1]
      name   := "main"
      params := [⟨"tid", .vec .uint 3, .svDispatchThreadId, none, none, .qIn⟩]
      body   :=
        [ .declInit (.scalar .uint) "i" (.member (.var "tid") "x")
        , .declInit (.scalar .half) "h"
            (.bin "*" (.index (.var "w") (.var "i")) (.litHalf 0.5))
        , .assign (.index (.var "o") (.var "i")) (.cast (.scalar .float) (.var "h"))
        , .ret none ]
    }] }

def halfArithShaderExpected : String :=
"[[vk::binding(0, 0)]]
StructuredBuffer<half> w;
[[vk::binding(1, 0)]]
RWStructuredBuffer<float> o;

[shader(\"compute\")] [numthreads(64, 1, 1)]
void main(uint3 tid : SV_DispatchThreadID) {
  uint i = tid.x;
  half h = (w[i] * 0.500000h);
  o[i] = float(h);
  return;
}"

example : LeanSlang.emit halfArithShader = halfArithShaderExpected := by
  native_decide

/-! ### DoubleSpline: a cubic in double

Horner evaluation of a cubic in `double`, with `double(...)` casts of
a float buffer read, signed integer literals and float literals; the
result is narrowed back to `float` for the store. -/

private def dparam (n : String) : SlangBinding :=
  ⟨n, .scalar .double, Semantic.none, none, none, .qIn⟩

def doubleSplineShader : SlangShaderModule :=
  { globals :=
      [ ⟨"x", .roBuf (.scalar .float), Semantic.none, some 0, some 0, .qIn⟩
      , ⟨"y", .rwBuf (.scalar .float), Semantic.none, some 1, some 0, .qIn⟩ ]
  , functions :=
      [ { retType := .scalar .double
        , name    := "horner3"
        , params  := [dparam "t", dparam "c0", dparam "c1", dparam "c2", dparam "c3"]
        , body    :=
            [ .retExpr
                (.bin "+"
                  (.bin "*"
                    (.bin "+"
                      (.bin "*"
                        (.bin "+" (.bin "*" (.var "c3") (.var "t")) (.var "c2"))
                        (.var "t"))
                      (.var "c1"))
                    (.var "t"))
                  (.var "c0")) ] }
      , { attrs  := [.shaderCompute, .numthreads 64 1 1]
        , name   := "main"
        , params := [⟨"tid", .vec .uint 3, .svDispatchThreadId, none, none, .qIn⟩]
        , body   :=
            [ .declInit (.scalar .uint) "i" (.member (.var "tid") "x")
            , .declInit (.scalar .double) "t"
                (.cast (.scalar .double) (.index (.var "x") (.var "i")))
            , .declInit (.scalar .double) "s"
                (.call "horner3"
                  [ .var "t"
                  , .cast (.scalar .double) (.litInt 1)
                  , .cast (.scalar .double) (.litInt (-3))
                  , .cast (.scalar .double) (.litFloat 0.5)
                  , .cast (.scalar .double) (.litFloat 0.25) ])
            , .assign (.index (.var "y") (.var "i")) (.cast (.scalar .float) (.var "s"))
            , .ret none ] } ] }

def doubleSplineShaderExpected : String :=
"[[vk::binding(0, 0)]]
StructuredBuffer<float> x;
[[vk::binding(1, 0)]]
RWStructuredBuffer<float> y;

double horner3(double t, double c0, double c1, double c2, double c3) {
  return ((((((c3 * t) + c2) * t) + c1) * t) + c0);
}

[shader(\"compute\")] [numthreads(64, 1, 1)]
void main(uint3 tid : SV_DispatchThreadID) {
  uint i = tid.x;
  double t = double(x[i]);
  double s = horner3(t, double(1), double((-3)), double(0.500000), double(0.250000));
  y[i] = float(s);
  return;
}"

example : LeanSlang.emit doubleSplineShader = doubleSplineShaderExpected := by
  native_decide

example : doubleSplineShader.entryPointName = "main" := by native_decide
