import CollatzFunction.Halt.TuringMachine10

namespace Halt

open Lean Meta Elab Tactic Std Term TmState

theorem E_zeroing (k : ℕ): ∀ (i : ℕ) (l r : List Γ) (init_cfg: Cfg),
nth_cfg init_cfg i = some ⟨E, ⟨Γ.one,
  Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero l),
  Turing.ListBlank.mk r⟩⟩ →
nth_cfg init_cfg (i + k + 1) = some ⟨E, ⟨Γ.zero,
  Turing.ListBlank.mk l,
  Turing.ListBlank.mk (List.replicate (k+1) Γ.zero ++ r)⟩⟩ := by
induction k with intros i l r init_cfg h
| zero => forward h
          ring_nf at *
          simp [h]
| succ k induction_step =>
            forward h
            apply induction_step at h
            ring_nf at *
            simp! [h]
            rw [List.append_cons]
            rw [← List.replicate_succ']
            ring_nf

end Halt
