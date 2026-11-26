import Lake.Check.Axioms
import Lake.Check.Compare

/- Run the same statement and axiom routines as Lean 4.35 Lake.CLI.Check.verifyMatch.
   Exit before launching the checkers, so their heaps cannot overlap with these maps.
   Input consists solely of exported declarations and target names. -/
private def primitives : Array Lean.Name := #[
  ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.gcd, ``Nat.div, ``Nat.mod,
  ``Nat.beq, ``Nat.ble, ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight,
  ``String.ofList, ``Char.ofNat, ``List, ``eagerReduce, ``Nat, ``String, ``String.mk, ``Char,
  ``optParam, ``autoParam, ``semiOutParam, ``outParam
]

def main (args : List String) : IO Unit := do
  let ref :: sol :: roots := args | throw (IO.userError "Expected a reference, solution, and theorem names")
  if roots.isEmpty then throw (IO.userError "Expected at least one theorem")
  let targets := roots.toArray.map String.toName
  let legal := #[``propext, ``Classical.choice, ``Quot.sound]
  let refEnv ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk ref .read)
  let solEnv ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk sol .read)
  IO.ofExcept <| Lake.Check.compareAt refEnv solEnv (targets ++ legal) #[] primitives
  IO.ofExcept <| Lake.Check.checkAxioms solEnv targets #[] legal
  IO.println s!"Matched target declarations and checked axiom dependencies: {targets}; allowlist: {legal}"
