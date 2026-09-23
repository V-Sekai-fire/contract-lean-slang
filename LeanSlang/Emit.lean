import LeanSlang.AST

/-!
# `LeanSlang.Emit` — pretty-printer to Slang source text.

Pure-Lean string builder. Output is intended to be syntactically
valid Slang accepted by `slangc -target spirv`. Layout choices
(indentation, semicolons, attribute order) are pinned by the
native_decide reference fixtures.
-/

namespace LeanSlang

/-! ## Scalar / SlangType / Semantic / SlangBinding -/

def emitScalar : Scalar → String
  | .float => "float"
  | .uint  => "uint"
  | .int   => "int"
  | .bool  => "bool"
  | .half  => "half"
  | .double => "double"

partial def emitSlangType : SlangType → String
  | .scalar s    => emitScalar s
  | .vec s n     => emitScalar s ++ toString n
  | .mat s r c   => emitScalar s ++ toString r ++ "x" ++ toString c
  | .rwBuf t     => "RWStructuredBuffer<" ++ emitSlangType t ++ ">"
  | .roBuf t     =>   "StructuredBuffer<" ++ emitSlangType t ++ ">"
  | .const sName => "ConstantBuffer<" ++ sName ++ ">"
  | .named n     => n

def emitSemantic : Semantic → String
  | .svDispatchThreadId => "SV_DispatchThreadID"
  | .svGroupThreadId    => "SV_GroupThreadID"
  | .svGroupId          => "SV_GroupID"
  | .none               => ""

/-- Emit a function-parameter binding. -/
def emitParamBinding (b : SlangBinding) : String :=
  let qual := match b.qualifier with
    | .qIn    => ""
    | .qOut   => "out "
    | .qInOut => "inout "
  let core := qual ++ emitSlangType b.type ++ " " ++ b.name
  match b.semantic with
  | .none => core
  | s     => core ++ " : " ++ emitSemantic s

/-- Emit a top-level / global binding. Adds the
    `[[vk::binding(b, space)]]` attribute when `binding` is set. -/
def emitGlobalBinding (b : SlangBinding) : String :=
  let attr :=
    match b.binding with
    | none   => ""
    | some i =>
        let space := b.space.getD 0
        "[[vk::binding(" ++ toString i ++ ", " ++ toString space ++ ")]]\n"
  attr ++ emitSlangType b.type ++ " " ++ b.name ++ ";"

/-! ## Expressions -/

/-- Text of a float literal: Lean's `Float` `toString`, with `.0`
    appended when it has neither a point nor an exponent. Shared by
    `litFloat` (as is) and `litHalf` (plus an `h` suffix). -/
def emitFloatText (v : Float) : String :=
  let s := toString v
  if s.contains '.' || s.contains 'e' || s.contains 'E' then s
  else s ++ ".0"

/-! ## Exact float literals

`emitFloatText` prints Lean's `Float.toString`, six decimal places,
so `1e-12` prints as `0.000000` and every constant with more than six
decimals is rounded. The exact forms below print the shortest decimal
that parses back to the same binary32 / binary64 value. All
arithmetic is on `Nat` (the value `m * 2^e` from the IEEE bits against
candidate decimals `d * 10^q`), so the result does not depend on any
float formatting or parsing routine. -/

namespace ExactFloat

/-- Compare `a * 2^x * 5^y` with `b * 2^z * 5^w`, exactly. -/
def cmp (a : Nat) (x y : Int) (b : Nat) (z w : Int) : Ordering :=
  let dx := x - z
  let dy := y - w
  compare (a * 2 ^ dx.toNat * 5 ^ dy.toNat) (b * 2 ^ (-dx).toNat * 5 ^ (-dy).toNat)

/-- A finite, nonzero magnitude `m * 2^e` together with the rounding
    interval of its format, scaled to units of `2^u`: every decimal
    strictly between `lo` and `hi` parses back to `m * 2^e`. -/
structure Interval where
  m  : Nat
  e  : Int
  u  : Int
  lo : Nat
  hi : Nat

/-- The acceptance interval of `m * 2^e` in a format whose significand
    has `p` bits. `narrow` marks the bottom of a binade, where the gap
    below is half the gap above. `margin` (in units of `2^(e-2-s)`)
    shrinks the interval from both ends; with `s = 28`, `margin = 2`
    is one binary64 ulp of a binary32 value, so a decimal inside the
    shrunk interval also survives slangc's decimal->double->float
    double rounding. With `s = 0`, `margin = 0` the interval is the
    open binary64 rounding interval. -/
def interval (m : Nat) (e : Int) (narrow : Bool) (s margin : Nat) : Interval :=
  let v  := m * 2 ^ (2 + s)
  let hi := v + 2 ^ (1 + s)
  let lo := v - (if narrow then 2 ^ s else 2 ^ (1 + s))
  { m, e, u := e - 2 - s, lo := lo + margin, hi := hi - margin }

/-- `d * 10^q` lies strictly inside the interval. -/
def accepts (iv : Interval) (d : Nat) (q : Int) : Bool :=
  cmp iv.lo iv.u 0 d q q == .lt && cmp d q q iv.hi iv.u 0 == .lt

/-- `P` with `10^P <= m * 2^e < 10^(P+1)`, for `m > 0`. -/
def decExp (m : Nat) (e : Int) : Int := Id.run do
  let bits : Int := (Nat.log2 m : Int) + e
  let mut p : Int := (bits * 30103) / 100000
  for _ in [0:8] do
    if cmp m e 0 1 p p == .lt then p := p - 1
  for _ in [0:8] do
    if cmp m e 0 1 (p + 1) (p + 1) != .lt then p := p + 1
  return p

/-- The shortest decimal `(d, q)` with `d * 10^q` inside the interval,
    trying 1 to 40 significant digits and, at each length, the two
    grid points that bracket the value, nearer first. `none` only if
    no length up to 40 fits (not reachable for binary32/64). -/
def shortest (iv : Interval) : Option (Nat × Int) := Id.run do
  let p := decExp iv.m iv.e
  for k in [1:41] do
    let q : Int := p - (k : Int) + 1
    let num := iv.m * 2 ^ (iv.e - q).toNat * 5 ^ (-q).toNat
    let den := 2 ^ (q - iv.e).toNat * 5 ^ q.toNat
    let fl := num / den
    let ce := if num % den == 0 then fl else fl + 1
    let (a, b) := if num - fl * den <= ce * den - num then (fl, ce) else (ce, fl)
    if a > 0 && accepts iv a q then return some (a, q)
    if b > 0 && accepts iv b q then return some (b, q)
  return none

/-- Decimal text of `d * 10^q`, always with a `.`: positional for
    decimal exponents in `[-5, 9)`, otherwise `d.ddde<X>`. -/
def decimalText (d : Nat) (q : Int) : String := Id.run do
  let mut d := d
  let mut q := q
  for _ in [0:400] do
    if d != 0 && d % 10 == 0 then
      d := d / 10
      q := q + 1
  let s := toString d
  let n : Int := s.length
  let x := q + n - 1
  let zeros (k : Nat) : String := String.ofList (List.replicate k '0')
  if -5 ≤ x && x < 9 then
    if q ≥ 0 then
      return s ++ zeros q.toNat ++ ".0"
    else if x ≥ 0 then
      let intLen := (n + q).toNat
      return (s.take intLen).toString ++ "." ++ (s.drop intLen).toString
    else
      return "0." ++ zeros (-x - 1).toNat ++ s
  else
    let tail := (s.drop 1).toString
    return (s.take 1).toString ++ "." ++ (if tail.isEmpty then "0" else tail)
      ++ "e" ++ toString x

/-- `slangc -target cpp` (2026.13.1) re-prints every float literal
    from its IR double: for `2^-17 <= |v| < 2^16` as fixed-point with
    17 decimal places (trailing zeros trimmed), otherwise as
    scientific with 18 significant digits. The fixed form keeps only
    `17 + log10 |v|` significant digits, too few for a binary64 below
    0.1, so e.g. `7.075852045090869e-5` reaches the C++ compiler as
    `0.00007075852045091`, 97 ulps off. True when that fixed form of
    this value would not parse back to it (binary32 values, which
    need 9 digits, are never affected). -/
def slangCppFixedLossy (iv : Interval) : Bool :=
  let inRange := cmp iv.m iv.e 0 1 (-17) 0 != .lt && cmp iv.m iv.e 0 1 16 0 == .lt
  if !inRange then false
  else
    let q : Int := -17
    let num := iv.m * 2 ^ (iv.e - q).toNat * 5 ^ (-q).toNat
    let den := 2 ^ (q - iv.e).toNat * 5 ^ q.toNat
    let fl := num / den
    let r2 := 2 * (num - fl * den)
    if r2 < den then !accepts iv fl q
    else if r2 > den then !accepts iv (fl + 1) q
    else !(accepts iv fl q && accepts iv (fl + 1) q)

/-- `0x` plus `w` upper-case hex digits of `n`. -/
def hex (w : Nat) (n : Nat) : String :=
  let ds := Nat.toDigits 16 n
  "0x" ++ (String.ofList (List.replicate (w - ds.length) '0' ++ ds)).toUpper

/-- Sign, parenthesis and suffix around the magnitude's text. -/
def wrap (neg : Bool) (mag suffix : String) : String :=
  if neg then "(-" ++ mag ++ suffix ++ ")" else mag ++ suffix

end ExactFloat

open ExactFloat in
/-- The `litFloatExact` text: `v` rounded to binary32 (`Float.toFloat32`,
    round to nearest even), then the shortest decimal inside that
    binary32's rounding interval shrunk by one binary64 ulp, plus `f`. -/
def emitFloat32Exact (v : Float) : String :=
  let b := v.toFloat32.toBits.toNat
  let neg := b >>> 31 == 1
  let ex := (b >>> 23) % 256
  let fr := b % 2 ^ 23
  if ex == 255 then "asfloat(" ++ hex 8 b ++ "u)"
  else if ex == 0 && fr == 0 then wrap neg "0.0" "f"
  else
    let (m, e) : Nat × Int :=
      if ex == 0 then (fr, -149) else (fr + 2 ^ 23, (ex : Int) - 150)
    let iv := interval m e (fr == 0 && ex > 1) 28 2
    match shortest iv with
    | some (d, q) => wrap neg (decimalText d q) "f"
    | none        => "asfloat(" ++ hex 8 b ++ "u)"

open ExactFloat in
/-- The `litDoubleExact` text: the shortest decimal inside `v`'s open
    binary64 rounding interval, plus `L`; or `asdouble(lo, hi)` when
    `slangc -target cpp` would re-print that value lossily
    (`ExactFloat.slangCppFixedLossy`), so the cpp and spirv targets
    both get the exact binary64. -/
def emitDoubleExact (v : Float) : String :=
  let b := v.toBits.toNat
  let neg := b >>> 63 == 1
  let ex := (b >>> 52) % 2048
  let fr := b % 2 ^ 52
  let bitcast := "asdouble(" ++ hex 8 (b % 2 ^ 32) ++ "u, " ++ hex 8 (b >>> 32) ++ "u)"
  if ex == 2047 then bitcast
  else if ex == 0 && fr == 0 then wrap neg "0.0" "L"
  else
    let (m, e) : Nat × Int :=
      if ex == 0 then (fr, -1074) else (fr + 2 ^ 52, (ex : Int) - 1075)
    let iv := interval m e (fr == 0 && ex > 1) 0 0
    if slangCppFixedLossy iv then bitcast
    else match shortest iv with
      | some (d, q) => wrap neg (decimalText d q) "L"
      | none        => bitcast

partial def emitExpr : SlangExpr → String
  | .litFloat v        => emitFloatText v
  | .litUint v         => toString v ++ "u"
  | .litBool true      => "true"
  | .litBool false     => "false"
  | .var name          => name
  | .index buf idx     => emitExpr buf ++ "[" ++ emitExpr idx ++ "]"
  | .member recv field => emitExpr recv ++ "." ++ field
  | .bin op l r        => "(" ++ emitExpr l ++ " " ++ op ++ " " ++ emitExpr r ++ ")"
  | .un op e           => "(" ++ op ++ emitExpr e ++ ")"
  | .call fn args      =>
      let argsStr := String.intercalate ", " (args.map emitExpr)
      fn ++ "(" ++ argsStr ++ ")"
  | .ternary c t f     =>
      "(" ++ emitExpr c ++ " ? " ++ emitExpr t ++ " : " ++ emitExpr f ++ ")"
  | .litHalf v         => emitFloatText v ++ "h"
  | .litInt v          => if v < 0 then "(" ++ toString v ++ ")" else toString v
  | .cast ty e         => emitSlangType ty ++ "(" ++ emitExpr e ++ ")"
  | .litFloatExact v   => emitFloat32Exact v
  | .litDoubleExact v  => emitDoubleExact v

/-! ## Statements -/

private def indent (n : Nat) : String :=
  String.ofList (List.replicate (2 * n) ' ')

private def openBrace : String := "{"
private def closeBrace : String := "}"

partial def emitStmt : Nat → SlangStmt → String
  | depth, .declare ty name init =>
      let lhs := indent depth ++ emitSlangType ty ++ " " ++ name
      match init with
      | some e => lhs ++ " = " ++ emitExpr e ++ ";"
      | none   => lhs ++ ";"
  | depth, .declarePrecise ty name init =>
      let lhs := indent depth ++ "precise " ++ emitSlangType ty ++ " " ++ name
      match init with
      | some e => lhs ++ " = " ++ emitExpr e ++ ";"
      | none   => lhs ++ ";"
  | depth, .declareArray elemTy name size =>
      indent depth ++ emitSlangType elemTy ++ " " ++ name
        ++ "[" ++ toString size ++ "];"
  | depth, .assign lhs rhs =>
      indent depth ++ emitExpr lhs ++ " = " ++ emitExpr rhs ++ ";"
  | depth, .expr e =>
      indent depth ++ emitExpr e ++ ";"
  | depth, .ret none =>
      indent depth ++ "return;"
  | depth, .ret (some e) =>
      indent depth ++ "return " ++ emitExpr e ++ ";"
  | depth, .ifThen cond thenS elseS =>
      let head := indent depth ++ "if (" ++ emitExpr cond ++ ") " ++ openBrace
      let thenBody := String.intercalate "\n" (thenS.map (emitStmt (depth + 1)))
      let close := indent depth ++ closeBrace
      let elseBlock :=
        if elseS.isEmpty then ""
        else
          let elseBody := String.intercalate "\n" (elseS.map (emitStmt (depth + 1)))
          " else " ++ openBrace ++ "\n" ++ elseBody ++ "\n" ++ close
      head ++ "\n" ++ thenBody ++ "\n" ++ close ++ elseBlock
  | depth, .forCount name initE boundE body =>
      let head :=
        indent depth ++ "for (uint " ++ name ++ " = " ++ emitExpr initE
        ++ "; " ++ name ++ " < " ++ emitExpr boundE
        ++ "; ++" ++ name ++ ") " ++ openBrace
      let bodyStr := String.intercalate "\n" (body.map (emitStmt (depth + 1)))
      let close := indent depth ++ closeBrace
      head ++ "\n" ++ bodyStr ++ "\n" ++ close
  | depth, .whileLoop cond body =>
      let head := indent depth ++ "while (" ++ emitExpr cond ++ ") " ++ openBrace
      let bodyStr := String.intercalate "\n" (body.map (emitStmt (depth + 1)))
      let close := indent depth ++ closeBrace
      head ++ "\n" ++ bodyStr ++ "\n" ++ close

/-! ## Function attributes / declarations / module -/

def emitFnAttr : FnAttr → String
  | .shaderCompute        => "[shader(\"compute\")]"
  | .numthreads x y z     =>
      "[numthreads(" ++ toString x ++ ", " ++ toString y ++ ", " ++ toString z ++ ")]"

def emitFunction (f : SlangFunctionDecl) : String :=
  let attrLine :=
    if f.attrs.isEmpty then ""
    else (String.intercalate " " (f.attrs.map emitFnAttr)) ++ "\n"
  let paramsStr := String.intercalate ", " (f.params.map emitParamBinding)
  let header :=
    attrLine ++ emitSlangType f.retType ++ " " ++ f.name
    ++ "(" ++ paramsStr ++ ") " ++ openBrace
  let bodyStr := String.intercalate "\n" (f.body.map (emitStmt 1))
  header ++ "\n" ++ bodyStr ++ "\n" ++ closeBrace

/-- Emit a struct declaration. Fields are indented two spaces. -/
def emitStruct (s : SlangStructDecl) : String :=
  let header := "struct " ++ s.name ++ " " ++ openBrace
  let fieldsStr := String.intercalate "\n"
    (s.fields.map (fun b => "  " ++ emitSlangType b.type ++ " " ++ b.name ++ ";"))
  header ++ "\n" ++ fieldsStr ++ "\n" ++ closeBrace ++ ";"

/-- Emit a `groupshared` workgroup-local declaration. -/
def emitGroupShared (g : SlangGroupSharedDecl) : String :=
  let head := "groupshared " ++ emitSlangType g.elemType ++ " " ++ g.name
  let dimsStr := g.dims.foldl (fun s n => s ++ "[" ++ toString n ++ "]") ""
  head ++ dimsStr ++ ";"

/-- Emit a complete shader module. Order: structs, groupshared,
    globals, functions — each non-empty section separated from the
    next by a blank line. -/
def emit (m : SlangShaderModule) : String :=
  let s := String.intercalate "\n\n" (m.structs.map emitStruct)
  let gs := String.intercalate "\n" (m.groupShared.map emitGroupShared)
  let g := String.intercalate "\n" (m.globals.map emitGlobalBinding)
  let f := String.intercalate "\n\n" (m.functions.map emitFunction)
  let parts := [s, gs, g, f].filter (fun p => !p.isEmpty)
  String.intercalate "\n\n" parts

end LeanSlang
