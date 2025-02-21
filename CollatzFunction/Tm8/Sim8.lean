import CollatzFunction.Tm8.TuringMachine8
import CollatzFunction.Basic

open Tm8

unsafe def foo (cfg : Cfg) : IO Unit :=
  do
    IO.println s!"{cfg}"
    foo (step machine cfg)


unsafe def main (args : List String) : IO Unit :=
  match args with
  | [] => IO.println s!"Please give a Nat"
  | n :: _ => match n.toNat? with
    | none => IO.println "Parse to Nat failed"
    | some n => foo (init (List.cons Γ.zero (List.replicate n Γ.one)))
