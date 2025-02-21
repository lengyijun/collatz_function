import CollatzFunction.Tm8.TuringMachine8
import CollatzFunction.Tm8.Transition
import CollatzFunction.Tm8.BStep

namespace Tm8

open Lean Meta Elab Tactic Std Term TmState Γ

private lemma copy_half_step (a i b: ℕ)(l: List Γ)(init_cfg: Cfg)
(h : nth_cfg init_cfg i =  ⟨G, ⟨one,
  Turing.ListBlank.mk (List.replicate (a+1) one ++ zero :: l),
  Turing.ListBlank.mk (List.replicate b one)⟩⟩) :
nth_cfg init_cfg (3 + i + b * 2) =  ⟨G, ⟨one,
  Turing.ListBlank.mk (List.replicate a one ++ zero :: l),
  Turing.ListBlank.mk (List.replicate (b+2) one)⟩⟩
:= by
rw [← (ListBlank_empty_eq_single_zero (List.replicate b one))] at h
apply G_to_J at h
forward h
simp [h]
rw [← List.cons_append]
rw [← List.replicate_succ]
rw [← List.replicate_one]
rw [List.replicate_append_replicate]

theorem copy_half (a : ℕ): ∀ (i b: ℕ)(l: List Γ)(init_cfg: Cfg),
nth_cfg init_cfg i =  ⟨G, ⟨one,
  Turing.ListBlank.mk (List.replicate a one ++ zero :: l),
  Turing.ListBlank.mk (List.replicate b one)⟩⟩ →
nth_cfg init_cfg (i + a * (2*a+2*b+1)) =  ⟨G, ⟨one,
  Turing.ListBlank.mk (zero :: l),
  Turing.ListBlank.mk (List.replicate (b+a*2) one)⟩⟩
:= by
induction a with intros i b l init_cfg h
| zero => simp_all
| succ a ih =>
  apply copy_half_step at h
  apply ih at h
  ring_nf at *
  rw [← h]

lemma B_odd (n: ℕ) (h_odd : Odd n): ∀ (i: ℕ)(l r: List Γ)(init_cfg: Cfg),
nth_cfg init_cfg i =  ⟨B, ⟨one,
  Turing.ListBlank.mk (zero :: l),
  Turing.ListBlank.mk (List.replicate n one ++ zero :: r)⟩⟩ →
nth_cfg init_cfg (i + (n^2 + 7 * n)/ 2 + 4) =  ⟨C, ⟨zero,
  Turing.ListBlank.mk (List.replicate ((n+1)/2) one ++ l),
  Turing.ListBlank.mk (List.replicate (1+(n+1)/2) one ++ r)⟩⟩
:= by
induction' n using Nat.strongRecOn with n IH
intros i l r init_cfg h
cases n with
| zero => tauto
| succ n => cases n with
  | zero => simp
            forward h
            forward h
            forward h
            forward h
            forward h
            forward h
            forward h
            forward h
            ring_nf
            simp [h]
  | succ n => ring_nf at h
              apply B_step at h
              specialize IH n (by omega)
              apply IH at h
              . ring_nf at *
                have g : (4 + i + (18 + n * 11 + n ^ 2) / 2) = (13 + i + n * 2 + (n * 7 + n ^ 2) / 2) := by omega
                rw [g]
                simp [h]
                have h : (3+n)/2 = (1+n)/2+1 := by omega
                rw [h]
                ring_nf
                rw [List.append_cons]
                rw [← List.replicate_one]
                rw [List.replicate_append_replicate]
                ring_nf
                rw [List.append_cons]
                rw [← List.replicate_one]
                rw [List.replicate_append_replicate]
                ring_nf
                tauto
              . obtain ⟨k, h_odd⟩ := h_odd
                cases k with
                | zero => omega
                | succ k => use k; omega

end Tm8
