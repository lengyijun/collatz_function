import CollatzFunction.NonHalt.TuringMachine9
import CollatzFunction.Basic

open NonHalt

unsafe def foo (cfg : Cfg) : IO Unit :=
match (step machine cfg) with
| some cfg => do
                IO.println s!"{cfg}"
                foo cfg
| none => IO.println s!"halt"


unsafe def main (args : List String) : IO Unit :=
  match args with
  | [] => IO.println s!"Please give a Nat"
  | n :: _ => match n.toNat? with
    | none => IO.println "Parse to Nat failed"
    | some n => if n = 0 then
                  IO.println "Please give a Nat > 0"
                else
                  foo (init (List.cons Γ.zero (List.replicate n Γ.one)))
