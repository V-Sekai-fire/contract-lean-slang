/-!
# `LeanSlang.Types` — Slang scalar / vector / matrix / buffer types

Pure data — no logic. Mirrors the subset of Slang's type system that
the DDM matvec shader (and similarly small compute kernels) need:

- Scalar: `Float`, `Uint`, `Int`, `Bool`, `Half`, `Double`.
- Vector: `Float3`, `Float4`, `Uint3`.
- Matrix: `Float4x4`.
- Buffer: `RWStructuredBuffer<T>`, `StructuredBuffer<T>` (read-only).
- Constant buffer: `ConstantBuffer<S>` for per-dispatch parameters.

Higher-level constructs (custom structs, samplers, textures, etc.)
are explicit out of scope — extend incrementally as new shaders need
them.
-/

namespace LeanSlang

/-- Scalar primitive types Slang supports out of the box.
    `half` and `double` are appended after the original four so the
    constructor order (and every existing match) is unchanged. -/
inductive Scalar
  | float
  | uint
  | int
  | bool
  /-- 16-bit float. slangc 2026.13 declares SPIR-V
      `UniformAndStorageBuffer16BitAccess` and `Float16` for a `half`
      storage buffer, even when the kernel only loads and widens. -/
  | half
  /-- 64-bit float. Needs SPIR-V `Float64`. -/
  | double
deriving Repr, BEq, DecidableEq, Inhabited

/-- The Slang type. We keep it small and add nodes only when a shader
    needs them. -/
inductive SlangType
  | scalar (s : Scalar)
  | vec    (s : Scalar) (n : Nat)         -- e.g. Float3 = vec float 3
  | mat    (s : Scalar) (rows cols : Nat) -- e.g. Float4x4 = mat float 4 4
  | rwBuf  (elem : SlangType)              -- RWStructuredBuffer<elem>
  | roBuf  (elem : SlangType)              --   StructuredBuffer<elem>
  | const  (struct_name : String)          -- ConstantBuffer<struct_name>
  | named  (n : String)                    -- a struct or alias by name
deriving Repr, BEq, Inhabited

/-- Slang built-in semantics for kernel entry-point parameters. -/
inductive Semantic
  | svDispatchThreadId
  | svGroupThreadId
  | svGroupId
  | none
deriving Repr, BEq, Inhabited

/-- Function-parameter direction qualifier. Slang inherits HLSL's
    `in` / `out` / `inout` semantics. -/
inductive ParamQualifier
  | qIn
  | qOut
  | qInOut
deriving Repr, BEq, Inhabited

/-- A function / shader parameter binding: name, type, optional
    semantic, optional register binding (e.g. `register(u0, space0)`),
    optional `out` / `inout` qualifier. -/
structure SlangBinding where
  name      : String
  type      : SlangType
  semantic  : Semantic := Semantic.none
  /-- Vulkan binding index when this parameter is a global buffer.
      `none` means "let Slang assign one automatically". -/
  binding   : Option Nat := none
  space     : Option Nat := none
  qualifier : ParamQualifier := ParamQualifier.qIn
deriving Repr, Inhabited

end LeanSlang
