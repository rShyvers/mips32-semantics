/-
ManualIndependence.lean -- the environment-level independence check of the manual spec (wave 12b).

Not a module of the build: `scripts/manual_deps.py` prepends `import` lines for every module under
`Semantics/Manual/` and runs the result with `lake env lean`. The check walks the constants the
`Manual.*` modules define, transitively through every constant they use (`getUsedConstants`; for a
theorem its statement only, a proof does not define behaviour), and fails (`logError`) on any constant
reached outside the allow-list:

* constants of the `Semantics.Manual.*` modules (walked further);
* constants of modules outside the project (core Lean, Std, Mathlib: not walked);
* `W32` (Word), `VAddr`/`PAddr` (Types);
* the `Instruction` type and what Lean generates for it (constructors, recursors, `casesOn`,
  `noConfusion`, `ctorIdx`, the derived `DecidableEq`/`Repr` instances) -- not the model's `decode`,
  `encode`, field extractors or CP0 register table, which live in the same module;
* the shared IEEE core of `Semantics/FpOps.lean` (`SHARED_FPOPS` below): the correctly rounded
  operations and conversions, the FCSR decoders `RoundingMode.ofBits` and `Flags.*`, the NaN
  classifiers and default NaNs, the formats. Not the model's FCSR helpers (`envOf`, `fpUpdate`, ...)
  nor its sign operations (`f32Abs`, ...).

A token scan cannot see through `open ... in`, namespaces or notation; this check reads the
elaborated environment, so it can.
-/
open Lean Meta Elab Command

/-- The shared items of `Semantics.FpOps` the spec may use (docs/MANUAL-SPEC.md). -/
def SHARED_FPOPS : List Name := [
  -- the IEEE environment, rounding-mode and flag decoders of the FCSR fields
  `Mips.Fp.Env, `Mips.Fp.Env.mk, `Mips.Fp.Env.RN, `Mips.Fp.Env.flush, `Mips.Fp.Env.rm,
  `Mips.Fp.Flags, `Mips.Fp.Flags.mk, `Mips.Fp.Flags.none, `Mips.Fp.Flags.invalidOnly,
  `Mips.Fp.Flags.ofBits, `Mips.Fp.Flags.toBits, `Mips.Fp.Flags.or,
  -- the field projections of the shared `Flags` structure (one per FCSR Cause/Flag bit V, Z, O, U, I):
  -- reading a field is part of using the shared type, like its constructor `Flags.mk`
  `Mips.Fp.Flags.invalid, `Mips.Fp.Flags.divZero, `Mips.Fp.Flags.overflow,
  `Mips.Fp.Flags.underflow, `Mips.Fp.Flags.inexact,
  `Mips.Fp.RoundingMode, `Mips.Fp.RoundingMode.ofBits,
  -- the formats
  `Mips.Fp.Format, `Mips.Fp.Format.isFinite, `Mips.Fp.Format.orderKey,
  `Mips.Fp.binary32, `Mips.Fp.binary64,
  -- the comparison relation
  `Mips.Fp.FpRel, `Mips.Fp.FpRel.equal, `Mips.Fp.FpRel.less, `Mips.Fp.FpRel.greater,
  `Mips.Fp.FpRel.unordered,
  -- NaN classifiers, default NaNs
  `Mips.Fp.isQNaN32, `Mips.Fp.isQNaN64, `Mips.Fp.isSNaN32, `Mips.Fp.isSNaN64,
  `Mips.Fp.defaultQNaN32, `Mips.Fp.defaultQNaN64,
  -- the correctly rounded IEEE operations and conversions
  `Mips.Fp.f32Add, `Mips.Fp.f32Sub, `Mips.Fp.f32Mul, `Mips.Fp.f32Div, `Mips.Fp.f32Sqrt,
  `Mips.Fp.f64Add, `Mips.Fp.f64Sub, `Mips.Fp.f64Mul, `Mips.Fp.f64Div, `Mips.Fp.f64Sqrt,
  `Mips.Fp.f32Relation, `Mips.Fp.f64Relation,
  `Mips.Fp.f32ToF64, `Mips.Fp.f64ToF32, `Mips.Fp.f32ToW32, `Mips.Fp.f64ToW32,
  `Mips.Fp.w32ToF32, `Mips.Fp.w32ToF64F,
  -- R6-5: the longword (L) conversions of the 64-bit FPU
  `Mips.Fp.f32ToW64, `Mips.Fp.f64ToW64, `Mips.Fp.w64ToF32, `Mips.Fp.w64ToF64,
  -- R6-6B: the Release 6 FP operations (fused multiply-add, maxNum/minNum/maxNumMag/minNumMag,
  -- class, roundToIntegralExact); CMP.condn.fmt is transcribed on `f32Relation`/`f64Relation`
  `Mips.Fp.f32Fma, `Mips.Fp.f64Fma, `Mips.Fp.f32MinMax, `Mips.Fp.f64MinMax,
  `Mips.Fp.Format.MinMaxOp, `Mips.Fp.Format.MinMaxOp.max, `Mips.Fp.Format.MinMaxOp.min,
  `Mips.Fp.Format.MinMaxOp.maxa, `Mips.Fp.Format.MinMaxOp.mina,
  `Mips.Fp.f32Class, `Mips.Fp.f64Class, `Mips.Fp.f32Rint, `Mips.Fp.f64Rint,
  -- the input flush of FCSR.FS (CMP.condn.fmt flushes without Inexact, Vol I-A §6.7.2.4, p.102)
  `Mips.Fp.Format.flushIn ]

/-- The model's types the spec may name. -/
def SHARED_TYPES : List Name := [`W32, `VAddr, `PAddr]

def isManualMod (m : Name) : Bool := (`Semantics.Manual).isPrefixOf m

/-- A constant Lean generates for the `Instruction` type (or the type itself). -/
def isInstructionAux (env : Environment) (n : Name) : Bool :=
  n == `Instruction ||
  (match env.find? n with
   | some (.ctorInfo c) => c.induct == `Instruction
   | _ => false) ||
  (n.getPrefix == `Instruction &&
    (isAuxRecursor env n || isNoConfusion env n || n.getString! == "ctorIdx" ||
     n.getString! == "rec" || n.getString! == "casesOn" || n.getString! == "noConfusionType" ||
     (n.getString!).startsWith "ctorElim" || n.getString! == "toCtorIdx")) ||
  (let s := n.toString
   s.startsWith "Instruction._sizeOf" || s.startsWith "instDecidableEqInstruction" || s.startsWith "instReprInstruction" ||
   (s.splitOn "decEqInstruction").length > 1 || (s.splitOn "reprInstruction").length > 1)

#eval show CommandElabM Unit from do
  let env ← getEnv
  let modOf (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx.toNat]!
  let manualMods := env.header.moduleNames.filter isManualMod
  if manualMods.isEmpty then
    logError "manual independence: no Semantics.Manual module imported"
    return
  let mut stack : Array Name := #[]
  for (n, _) in env.constants.toList do
    if let some m := modOf n then
      if isManualMod m then stack := stack.push n
  let roots := stack.size
  let mut seen : NameSet := {}
  let mut bad : Std.HashMap Name Name := {}   -- violating constant ↦ the constant using it
  repeat
    let some n := stack.back? | break
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let used : NameSet := match ci with
      | .thmInfo t => t.type.getUsedConstantsAsSet
      | _ => ci.getUsedConstantsAsSet
    for c in used do
      if seen.contains c then continue
      match modOf c with
      | none => stack := stack.push c        -- defined in this file: none expected
      | some m =>
        if isManualMod m then
          stack := stack.push c
        else if !(`Semantics).isPrefixOf m then
          pure ()                              -- core Lean / Std / Mathlib
        else if SHARED_TYPES.contains c || SHARED_FPOPS.contains c then
          pure ()
        else if m == `Semantics.Instruction && isInstructionAux env c then
          pure ()
        else
          unless bad.contains c do bad := bad.insert c n
  let viol := bad.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  for (c, by_) in viol do
    logError m!"INDEPENDENCE: {by_} (module {modOf by_}) uses {c} (module {modOf c})"
  logInfo m!"manual independence (environment): {manualMods.size} modules, {roots} constants, {seen.size} reached, {viol.size} violation(s)"
