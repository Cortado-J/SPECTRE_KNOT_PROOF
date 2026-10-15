/-
Lists the declarations of `SpectreKnot` that the nine main results do not use: `theoremA`, `theoremB`,
`theoremB_sharp`, `nestModel`, `theoremB_strand`, `chainModel`, `theoremA_strand`, `theoremB_exact` and `grandparent`.
Run from `lean/` with

    lake env lean tools/unused.lean

It follows every constant named in the types and proofs, starting from those nine. Compiler-generated declarations
and the generated data files are left out. One blind spot: a `@[simp]` lemma proved by `rfl` leaves no trace in the
proofs that use it (`iter_zero` is such a lemma, used by `iter_add`), so it is listed even when it is needed.
-/
import Lean
import SpectreKnot

open Lean Elab Command

/-- Every constant reachable from `todo` through types and values. -/
partial def reach (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then reach env rest seen
    else match env.find? n with
      | none => reach env rest (seen.insert n)
      | some info => reach env (info.getUsedConstantsAsSet.toList ++ rest) (seen.insert n)

/-- Declarations the compiler makes, not written by hand. -/
def generated (n : Name) : Bool :=
  n.isInternal || n.isInternalDetail ||
  match n with
  | .str _ s => ["rec", "recOn", "casesOn", "noConfusion", "noConfusionType", "below", "brecOn", "ibelow",
      "binductionOn", "injEq", "inj", "sizeOf_spec", "ctorIdx", "toCtorIdx", "ofNat_ctorIdx", "ofNat", "toNat", "mk",
      "elim", "ctorElim", "ctorElimType", "repr", "decEq"].contains s ||
      s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_" || s.startsWith "inst" || s.startsWith "_"
  | _ => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let roots := [`SpectreKnot.Statement.theoremA, `SpectreKnot.Statement.theoremB,
    `SpectreKnot.Statement.theoremB_sharp, `SpectreKnot.Statement.nestModel, `SpectreKnot.Statement.theoremB_strand,
    `SpectreKnot.Statement.chainModel, `SpectreKnot.Statement.theoremA_strand, `SpectreKnot.Statement.theoremB_exact,
    `SpectreKnot.Statement.grandparent]
  let used := reach env roots {}
  let modules := env.header.moduleNames
  let mut unused : Array (String × String) := #[]
  for (n, info) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := modules[idx.toNat]!
    unless (`SpectreKnot).isPrefixOf m && !(`SpectreKnot.Data).isPrefixOf m do continue
    if generated n || used.contains n || (env.getProjectionFnInfo? n).isSome then continue
    if info matches .ctorInfo _ then continue
    unused := unused.push (m.toString, n.toString)
  for (m, n) in unused.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)) do
    IO.println s!"{m}  {n}"
  IO.println s!"{unused.size} declarations not used by the main results"
