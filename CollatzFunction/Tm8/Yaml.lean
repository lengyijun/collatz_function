import CollatzFunction.Tm8.TuringMachine8
import CollatzFunction.Basic
import Init.Data.List.Basic

open Tm8

open Lean Meta Elab Tactic Std Term TmState

instance : ToString Turing.Dir where
  toString 
    | Turing.Dir.left => "L"
    | Turing.Dir.right => "R"

def foo : List TmState -> IO Unit
| [] => pure ()
| state :: xs => do
  IO.println s!"  {state}:"
  let stmt <- pure (machine state Γ.zero)
  IO.println s!"    0: \{write: {stmt.2.2}, {stmt.2.1}: {stmt.1}}"
  let stmt <- pure (machine state Γ.one)
  IO.println s!"    1: \{write: {stmt.2.2}, {stmt.2.1}: {stmt.1}}"
  foo xs


def main : List String → IO Unit
| _ => do
IO.println "blank: '0'"
IO.println "start state: G"
IO.println "input: 01111"
IO.println ""
IO.println "table:"
foo [
   A,
   B,
   C,
   D,
   E,
   G,
   H,
   J]

