-- theorem of recursive states
-- all these states' usage is to search 0
import CollatzFunction.Halt.TuringMachine10

namespace Halt

open Lean Meta Elab Tactic Std Term TmState


-- left
theorem recD (k : ℕ): ∀ (i : ℕ) (l r : List Γ) (init_cfg: Cfg),
nth_cfg init_cfg i = some ⟨D, ⟨Γ.one,
  Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero l),
  Turing.ListBlank.mk r⟩⟩ →
nth_cfg init_cfg (i + k + 1) = some ⟨D, ⟨Γ.zero,
  Turing.ListBlank.mk l,
  Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ r)⟩⟩ := by
induction k with intros i l r init_cfg h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) l (List.cons Γ.one r)
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ']
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

theorem recJ (k : ℕ): ∀ (i : ℕ) (l r : List Γ) (init_cfg),
nth_cfg init_cfg i = some ⟨J, ⟨Γ.one,
  Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero l),
  Turing.ListBlank.mk r⟩⟩ →
nth_cfg init_cfg (i + k + 1) = some ⟨J, ⟨Γ.zero,
  Turing.ListBlank.mk l,
  Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ r)⟩⟩ := by
induction k with intros i l r init_cfg h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) l (List.cons Γ.one r)
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ']
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]


--right
theorem recB (k : ℕ): ∀ (i : ℕ) (l r : List Γ) (init_cfg),
nth_cfg init_cfg i = some ⟨B, ⟨Γ.one,
  Turing.ListBlank.mk l,
  Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero r) ⟩⟩ →
nth_cfg init_cfg (i + k + 1) = some ⟨B, ⟨Γ.zero,
  Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ l),
  Turing.ListBlank.mk r⟩⟩ := by
induction k with intros i l r init_cfg h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) (List.cons Γ.one l) r
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ']
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]

theorem recH (k : ℕ): ∀ (i : ℕ) (l r : List Γ) (init_cfg: Cfg),
nth_cfg init_cfg i = some ⟨H, ⟨Γ.one,
  Turing.ListBlank.mk l,
  Turing.ListBlank.mk (List.replicate k Γ.one ++ List.cons Γ.zero r) ⟩⟩ →
nth_cfg init_cfg (i + k + 1) = some ⟨H, ⟨Γ.zero,
  Turing.ListBlank.mk (List.replicate (k+1) Γ.one ++ l),
  Turing.ListBlank.mk r⟩⟩ := by
induction k with intros i l r init_cfg h
| zero => simp [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]
| succ k induction_step =>
            specialize induction_step (i+1) (List.cons Γ.one l) r
            have g : i + (k+1) +1 = i + 1 + k + 1 := by omega
            rw [g, induction_step]
            . simp [List.replicate_succ']
            . simp! [nth_cfg, h, step, machine, Turing.Tape.write, Turing.Tape.move]


end Halt
