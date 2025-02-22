-- theorem of recursive states
-- all these states' usage is to search 0
import CollatzFunction.NonHalt.TuringMachine9

namespace NonHalt

open Lean Meta Elab Tactic Std Term TmState


-- left
theorem recD (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i =  ⟨D, ⟨Γ.one,
  Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero l),
  Turing.ListBlank.mk r⟩⟩ →
nth_cfg (i + k + 1) =  ⟨D, ⟨Γ.zero,
  Turing.ListBlank.mk l,
  Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ r)⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) l (List.cons Γ.one r)
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ']
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

theorem recJ (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i =  ⟨J, ⟨Γ.one,
  Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero l),
  Turing.ListBlank.mk r⟩⟩ →
nth_cfg (i + k + 1) =  ⟨J, ⟨Γ.zero,
  Turing.ListBlank.mk l,
  Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ r)⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) l (List.cons Γ.one r)
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ']
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]


--right
theorem recB (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i =  ⟨B, ⟨Γ.one,
  Turing.ListBlank.mk l,
  Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero r) ⟩⟩ →
nth_cfg (i + k + 1) =  ⟨B, ⟨Γ.zero,
  Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ l),
  Turing.ListBlank.mk r⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) (List.cons Γ.one l) r
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ']
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

theorem recH (k : ℕ): ∀ (i : ℕ) (l r : List Γ),
nth_cfg i =  ⟨H, ⟨Γ.one,
  Turing.ListBlank.mk l,
  Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero r) ⟩⟩ →
nth_cfg (i + k + 1) =  ⟨H, ⟨Γ.zero,
  Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ l),
  Turing.ListBlank.mk r⟩⟩ := by
induction k with intros i l r h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) (List.cons Γ.one l) r
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ']
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]


end NonHalt
