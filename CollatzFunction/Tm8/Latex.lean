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
  let stmt_0 <- pure (machine state Γ.zero)
  let stmt_1 <- pure (machine state Γ.one)
  IO.println s!"${state}$ & {stmt_0.2.2}{stmt_0.2.1}${stmt_0.1}$ & {stmt_1.2.2}{stmt_1.2.1}${stmt_1.1}$ \\\\"
  IO.println "\\hline"
  foo xs


def main : List String → IO Unit
| _ => do
IO.println "\\begin{center}"
IO.println "\\begin{tabular}{|c|c|c|}"
IO.println "\\hline"
IO.println "$M_8$ &  0  &   1   \\\\"
IO.println "\\hline"
foo [
   A,
   B,
   C,
   D,
   E,
   G,
   H,
   J]
IO.println "\\end{tabular}"
IO.println "\\end{center}"

