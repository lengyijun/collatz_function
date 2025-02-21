import CollatzFunction.Halt.TuringMachine10
import CollatzFunction.Basic
import Init.Data.List.Basic

open Halt

open Lean Meta Elab Tactic Std Term TmState

unsafe def foo (cfg : Cfg) (unvisited : List (TmState × Γ)): IO Unit :=
do
  IO.println s!"{cfg}"
  let unvisited <- pure (List.removeAll unvisited [⟨cfg.q, cfg.tape.head⟩])
  IO.println s!"{unvisited}"
  match (step machine cfg) with
  | some cfg => foo cfg unvisited
  | none => IO.println s!"halt"


unsafe def main : List String → IO Unit
| _ => foo (init (List.cons Γ.zero (List.replicate 21 Γ.one))) ([
   A,
   B,
   C,
   D,
   E,
   F,
   G,
   H,
   J,
   K].map (fun q => [⟨q, Γ.zero⟩, ⟨q, Γ.one⟩])).flatten
