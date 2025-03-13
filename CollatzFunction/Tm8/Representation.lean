import CollatzFunction.Tm8.TuringMachine8
import CollatzFunction.Tm8.Even
import CollatzFunction.Tm8.Odd
import CollatzFunction.Tm8.Search0
import CollatzFunction.Tm8.Transition
import CollatzFunction.Collatz
import CollatzFunction.ListBlank

namespace Tm8

open Lean Meta Elab Tactic Std Term TmState Γ

-- `nth_cfg i cfg` represent `n`
def nth_cfg_is_n (i n: Nat) (init_cfg : Cfg) :=
∃ l,
nth_cfg init_cfg i = ⟨G, ⟨zero, Turing.ListBlank.mk (zero :: l), Turing.ListBlank.mk (List.replicate n one)⟩⟩

end Tm8
