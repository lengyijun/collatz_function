-- theorem of recursive states
-- all these states' usage is to search 1
import CollatzFunction.NonHalt.TuringMachine9

namespace NonHalt

open Lean Meta Elab Tactic Std Term TmState

--right
theorem recF (k : ℕ): ∀ (i : ℕ) (l r : List Γ) (γ : Γ),
nth_cfg i = some ⟨F, ⟨Γ.zero,
  Turing.ListBlank.mk l,
  Turing.ListBlank.mk (List.replicate k Γ.zero ++ List.cons γ r) ⟩⟩ →
nth_cfg (i + k + 1) = some ⟨F, ⟨γ,
  Turing.ListBlank.mk (List.replicate (k+1) Γ.zero ++ l),
  Turing.ListBlank.mk r⟩⟩ := by
induction k with intros i l r γ h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) (List.cons Γ.zero l) r γ
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ']
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]


end NonHalt
