import CollatzFunction.Tm8.TuringMachine8
import CollatzFunction.Tm8.BStep

namespace Tm8

open Lean Meta Elab Tactic Std Term TmState Γ

lemma B_even (n: ℕ) (h_even : Even n): ∀ (i: ℕ)(l r: List Γ)(init_cfg: Cfg),
nth_cfg init_cfg i =  ⟨B, ⟨one,
  Turing.ListBlank.mk (zero :: l),
  Turing.ListBlank.mk (List.replicate n one ++ zero :: r)⟩⟩ →
nth_cfg init_cfg (i+ (n^2)/2 + 7 * n/2 + 4) =  ⟨A, ⟨zero,
  Turing.ListBlank.mk (List.replicate (1+n/2) one ++ l),
  Turing.ListBlank.mk (List.replicate (1+n/2) one ++ r)⟩⟩
:= by
induction' n using Nat.strongRecOn with n IH
intros i l r init_cfg h
cases n with
| zero => simp
          forward h
          forward h
          forward h
          forward h
          ring_nf
          simp [h]
| succ n => cases n with
  | zero => tauto
  | succ n => ring_nf at h
              apply B_step at h
              specialize IH n (by omega)
              apply IH at h
              . ring_nf at *
                have g : (4 + i + (4 + n * 4 + n ^ 2) / 2 + (14 + n * 7) / 2) = (13 + i + n * 2 + n ^ 2 / 2 + n * 7 / 2) := by omega
                rw [g]
                simp [h]
                rw [List.append_cons]
                rw [← List.replicate_one]
                rw [List.replicate_append_replicate]
                rw [List.append_cons]
                rw [← List.replicate_one]
                rw [List.replicate_append_replicate]
                tauto
              . obtain ⟨k, h_even⟩ := h_even
                cases k with
                | zero => omega
                | succ k => use k; omega

end Tm8
