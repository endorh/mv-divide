import Lean
import Lean.Elab.Tactic.Rewrite
import Mathlib.Lean.EnvExtension
import Mathlib.Lean.Expr.ReplaceRec
import Mathlib.Lean.Meta.Simp
import Std.Tactic.CoeExt
import Std.Tactic.Ext.Attr

import MvDivide.Correctness.CorrectResult

-- We don't use the `cfg` variable in many functions, but it's still intended to pass it around
set_option linter.unusedVariables false

open Lean Meta Elab Command Std Qq Tactic

/-!
The `alg` attribute.

Generates auxiliary definitions for an algorithm declared with `CorrectResult` type, which can be
used with the `such_that` and `correct_by` syntax to implement an algorithm along its proof of
correctness.
The `alg` attribute generates a pure version of the algorithm with its raw type, as well as a
separate lemma that asserts this variant is correct, using the original definition as proof.
-/
namespace AlgAttr
section Notation

-- Arguably, we should support the application of arbitrary attributes to both declarations,
-- but we only support applying `simp` to the spec declaration.

/-- Specify the `simp` attribute to be used for the spec declaration. -/
syntax algRest := ("(" "simp" " := " attr ")")?
/-- The `alg` attribute. Generates auxiliary definitions for an algorithm declared with
`CorrectResult`, which can be used with the `such_that` and `correct_by` syntax to implement
an algorithm along its proof of correctness. -/
syntax (name := alg) "alg" algRest : attr
/-- Abbreviation for `alg (simp := simp)`. -/
macro "alg" "simp" : attr => `(attr| alg (simp := simp))

end Notation

section Trace

initialize registerTraceClass `alg

end Trace

structure Config where
  -- The `Syntax` node corresponding to the `alg` attribute, required for LSP features.
  ref : Syntax
  -- The optional simp attribute `Syntax` applied to the generated spec declaration.
  simpStx : Option Syntax := none
deriving Repr

/-- Parse config from attribute application. -/
def elabConfig (stx : Syntax) : Config := match stx with
| `(attr| alg%$a (simp := $s)) => {
  simpStx := s
  ref := a }
| _ => { ref := stx }

/-- Removes the `_alg` suffix of a name. -/
def getBaseName (cfg : Config) (src : Name) : CoreM Name := do
  unless (src.toString (escape := false)).endsWith "_alg" do
    throwError "An `alg` declaration is expected to be named with an `_alg` suffix."
  return src.updateLast λs => s.dropRight 4

/-- The alg name consists of the name of the source, once removed the `_alg` suffix. -/
def getAlgName (cfg : Config) (base : Name) : Name :=
  base

/-- The spec name consists of the base name followed by `_spec`. -/
def getSpecName (cfg : Config) (base : Name) : Name :=
  base.updateLast λs => s ++ "_spec"

/-- Extracts the `res` type of a `CorrectResult` definition -/
def getAlgType (src : Expr) : MetaM Expr := do
  forallTelescope src λxs e => do
    match ← whnf e with
    -- Unfortunately, `Qq` doesn't yet support matching expressions
    -- | q(CorrectResult $type _) =>
    | .app (.app (.const ``CorrectResult _) type) _ =>
      return ←mkForallFVars xs type
    | _ => throwError "`alg` can only be used with declarations of type `CorrectResult` (using `such_that` to specify a correctness condition after the type)"

/-! Modified version of `Lean.Meta.mkAppM`, with an `explicit` parameter that can be used to
suppress implicit parameters' synthesis.
I couldn't get `Lean.Meta.mkAppM` to work otherwise. -/
section mkAppM

/-- Copy of `private Lean.Meta.mkFun`, to be used in `mkAppM` -/
private def mkFun (constName : Name) : MetaM (Expr × Expr) := do
  let cinfo ← getConstInfo constName
  let us ← cinfo.levelParams.mapM fun _ => mkFreshLevelMVar
  let f := mkConst constName us
  let fType ← instantiateTypeLevelParams cinfo us
  return (f, fType)

/-- Copy of `private Lean.Meta.mkAppMFinal`, to be used in `mkAppMArgs` -/
private def mkAppMFinal (methodName : Name) (f : Expr) (args : Array Expr) (instMVars : Array MVarId) : MetaM Expr := do
  instMVars.forM fun mvarId => do
    let mvarDecl ← mvarId.getDecl
    let mvarVal  ← synthInstance mvarDecl.type
    mvarId.assign mvarVal
  let result ← instantiateMVars (mkAppN f args)
  if (← hasAssignableMVar result) then throwError ("result contains metavariables" ++ indentExpr result)
  return result

/-- Modified version of `private Lean.Meta.mkAppMArgs`, with an `explicit` parameter that
can be used to suppress implicit parameters' synthesis. -/
private partial def mkAppMArgs (f : Expr) (fType : Expr) (xs : Array Expr) (explicit := false) : MetaM Expr :=
  let rec loop (type : Expr) (i : Nat) (j : Nat) (args : Array Expr) (instMVars : Array MVarId) : MetaM Expr := do
    if i >= xs.size then
      mkAppMFinal `mkAppM f args instMVars
    else match type with
      | Expr.forallE n d b bi =>
        let d  := d.instantiateRevRange j args.size args
        -- Here `explicit` can suppress the implicit nature of the binders
        match explicit, bi with
        | false, BinderInfo.implicit     =>
          let mvar ← mkFreshExprMVar d MetavarKind.natural n
          loop b i j (args.push mvar) instMVars
        | false, BinderInfo.strictImplicit     =>
          let mvar ← mkFreshExprMVar d MetavarKind.natural n
          loop b i j (args.push mvar) instMVars
        | false, BinderInfo.instImplicit =>
          let mvar ← mkFreshExprMVar d MetavarKind.synthetic n
          loop b i j (args.push mvar) (instMVars.push mvar.mvarId!)
        | _, _ =>
          let x := xs[i]!
          let xType ← inferType x
          if (← isDefEq d xType) then
            loop b (i+1) j (args.push x) instMVars
          else
            throwAppTypeMismatch (mkAppN f args) x
      | type =>
        let type := type.instantiateRevRange j args.size args
        let type ← whnfD type
        if type.isForall then
          loop type i args.size args instMVars
        else
          throwError s!"too many explicit arguments provided to{←ppExpr f}\narguments{←xs.mapM ppExpr}"
  loop fType 0 0 #[] #[]

/-- Modified version of `Lean.Meta.mkAppM`, with an `explicit` parameter that can be used to
suppress implicit parameters' synthesis.

Return the application `constName xs`.
It tries to fill the implicit arguments before the last element in `xs`.

Remark:
``mkAppM `arbitrary #[α]`` returns `@arbitrary.{u} α` without synthesizing
the implicit argument occurring after `α`.
Given a `x : (([Decidable p] → Bool) × Nat`, ``mkAppM `Prod.fst #[x]`` returns `@Prod.fst ([Decidable p] → Bool) Nat x`
-/
def mkAppM (constName : Name) (xs : Array Expr) (explicit := false) : MetaM Expr := do
  withNewMCtxDepth do
    let (f, fType) ← mkFun constName
    -- We simply pass `explicit` to our modified `mkAppMArgs`
    mkAppMArgs f fType xs (explicit := explicit)
end mkAppM

/-- Extracts the `correctness` type of a `CorrectResult` definition. -/
def getSpecType (algName : Name) (src : Expr) : MetaM Expr := do
  forallTelescope src λxs e => do
    match ← whnf e with
    -- Unfortunately, `Qq` doesn't yet support matching expressions
    -- | q(CorrectResult _ $spec) =>
    | .app (.app (.const ``CorrectResult _) _) spec =>
      let mut e : Expr := .app spec (←mkAppM algName xs (explicit := true))
      -- We use `whnf` to β-reduce the lambda application
      e ← whnf e
      return ←mkForallFVars xs e
    | _ => throwError "`alg` can only be used with declarations of type `CorrectResult` (using `such_that` to specify a correctness condition after the type)"

/-- Calls the source declaration and extracts its `res`. -/
def getAlgValue (algName : Name) (src : Expr) : MetaM Expr := do
  lambdaTelescope src λxs _ => do
    let e := .proj ``CorrectResult 0 (←mkAppM algName xs (explicit := true))
    return ←mkLambdaFVars xs e

/-- Calls the source declaration and extracts its `correctness`.
No further transformation is required thanks to definitional equality. -/
def getSpecValue (srcName : Name) (src specType : Expr) : MetaM Expr := do
  lambdaTelescope src λxs _ => do
    let m ← mkFreshExprMVar (some (←instantiateForall specType xs))
    let id := m.mvarId!
    id.assign (.proj ``CorrectResult 1 (←mkAppM srcName xs (explicit := true)))
    return ←mkLambdaFVars xs m

/-- Create the pure algorithm declaration. -/
def createAlgDecl (cfg : Config) (src tgt : Name) (decl : ConstantInfo) : MetaM ConstantInfo := do
  let mut decl := decl.updateName tgt
  decl := decl.updateType <| ←getAlgType decl.type
  if let some v := decl.value? then
    decl := decl.updateValue <| ←getAlgValue src v
  else throwError "`alg` does not support opaque/sorry definitions."
  return decl

/-- Create the correctness lemma. -/
def createSpecDecl (cfg : Config) (src alg tgt : Name) (srcDecl : ConstantInfo) : MetaM ConstantInfo := do
  let mut decl := srcDecl.updateName tgt
  decl := decl.updateType <| ←getSpecType alg srcDecl.type
  let some srcV := srcDecl.value? | throwError "`alg` does not support opaque/sorry definitions."
  decl := decl.updateValue <| ←getSpecValue src srcV decl.type
  return decl

/-- Add generated declarations. -/
def addAlgDeclarations (cfg : Config) (src alg spec : Name) : AttrM Unit := do
  let env ← getEnv
  if env.contains alg then
    trace[alg] "Algorithm declaration `{alg}` already exists, will be skipped."
  if env.contains spec then
    trace[alg] "Spec declaration `{spec}` already exists, will be skipped."
  let srcDecl ← getConstInfo src
  let algDeclInfo ← MetaM.run' <| createAlgDecl cfg src alg srcDecl
  let algDecl := algDeclInfo.toDeclaration!
  addDecl algDecl
  unless isNoncomputable env src do try
    compileDecl algDecl
  catch
  -- We cannot trust `isNoncomputable` because it's not reliable if the src
  -- is in a `noncomputable section` rather than being explicitly marked as `noncomputable`
  -- There should be a better way to filter exceptions than *by message*
  | .error s m =>
    if ToString.toString (←m.format) |>.startsWith "failed to compile definition" then
      trace[alg] "Source declaration is not computable! Compilation will be skipped."
      setEnv <| addNoncomputable (←getEnv) alg
    else throw (Exception.error s m)
  | e => throw e
  let specDeclInfo ← MetaM.run' <| createSpecDecl cfg src alg spec srcDecl
  let specDecl := specDeclInfo.toDeclaration!
  addDecl specDecl
  unless isNoncomputable env alg do
    compileDecl specDecl
  -- Add declaration ranges for LSP
  -- Unfortunately, it only works one-way, using 'Go to references...' from the
  -- attribute doesn't include the references to each of the declarations.
  addDeclarationRanges alg {
    range := ←getDeclarationRange (←getRef)
    selectionRange := ←getDeclarationRange cfg.ref }
  addDeclarationRanges spec {
    range := ←getDeclarationRange (←getRef)
    selectionRange := ←getDeclarationRange cfg.ref }
  if isProtected (←getEnv) src then
    setEnv <| addProtected (←getEnv) alg
    setEnv <| addProtected (←getEnv) spec

/-- Apply attributes to the generated declarations. -/
def applySimpAttribute (simpStx : Syntax) (spec : Name) : MetaM PUnit := do
  let _ ← Simp.addSimpAttrFromSyntax spec simpExtension .global simpStx
  return

/-- Apply the `alg` attribute to a definition. -/
def addAlgAttr (src : Name) (cfg : Config) (kind : AttributeKind) : AttrM Unit := do
  if src.isInternal' then
    trace[alg] "Skipping application to internal auxiliary declaration: {src.toString (escape := false)}"
    return
  unless kind == AttributeKind.global do
    throwError "`alg` can only be used as a global attribute"
  let baseName ← getBaseName cfg src
  let algName := getAlgName cfg baseName
  let specName := getSpecName cfg baseName
  addAlgDeclarations cfg src algName specName
  -- Apply `simp` attribute to the spec
  if let some s := cfg.simpStx then
    MetaM.run' <| applySimpAttribute s specName
  -- Add LSP pop-ups for the generated declarations located at the attribute
  -- For some reason, only the first one is displayed
  addConstInfo cfg.ref algName
  addConstInfo cfg.ref specName

end AlgAttr

/-- Register the `alg` attribute -/
initialize registerBuiltinAttribute {
  name := `alg
  descr := "Generate additional declarations for a correct algorithm (with type `CorrectResult`)"
  add := fun src stx kind => AlgAttr.addAlgAttr src (AlgAttr.elabConfig stx) kind
  -- We can't apply after compilation, because within non-computable sections
  -- it doesn't apply the attribute in time (when needed by a following declaration)
  -- It must be after elaboration, since we need the type and value to be already elaborated
  applicationTime := .afterTypeChecking
}