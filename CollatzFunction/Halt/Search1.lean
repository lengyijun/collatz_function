-- theorem of recursive states
-- all these states' usage is to search 1
import CollatzFunction.Halt.TuringMachine10

namespace Halt

open Lean Meta Elab Tactic Std Term TmState

--right
theorem recF (k : ℕ): ∀ (i : ℕ) (l r : List Γ) (init_cfg: Cfg) (γ : Γ),
nth_cfg init_cfg i = some ⟨F, ⟨Γ.zero,
  Turing.ListBlank.mk l,
  Turing.ListBlank.mk (List.replicate k Γ.zero ++ List.cons γ r) ⟩⟩ →
nth_cfg init_cfg (i + k + 1) = some ⟨F, ⟨γ,
  Turing.ListBlank.mk (List.replicate (k+1) Γ.zero ++ l),
  Turing.ListBlank.mk r⟩⟩ := by
induction k with intros i l r init_cfg γ h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) (List.cons Γ.zero l) r init_cfg γ
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ']
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]


end Halt
