import CollatzFunction.Halt.TuringMachine10
import CollatzFunction.Halt.Transition
import CollatzFunction.Halt.BStep

namespace Halt

open Lean Meta Elab Tactic Std Term TmState Γ

private lemma copy_half_step (a i b: ℕ)
(h : nth_cfg i = some ⟨G, ⟨one,
  Turing.ListBlank.mk (List.replicate (a+1) one),
  Turing.ListBlank.mk (List.replicate b one)⟩⟩) :
nth_cfg (3 + i + b * 2) = some ⟨G, ⟨one,
  Turing.ListBlank.mk (List.replicate a one),
  Turing.ListBlank.mk (List.replicate (b+2) one)⟩⟩
:= by
have g := lemma_G_to_H [] b
rw [ListBlank_empty_eq_single_zero] at g
apply g at h
apply lemma_H_to_J at h
forward h
simp [h]
rw [← List.cons_append]
rw [← List.replicate_succ]
rw [← List.replicate_one]
rw [List.replicate_append_replicate]

theorem copy_half (a : ℕ): ∀ (i b: ℕ),
nth_cfg i = some ⟨G, ⟨one,
  Turing.ListBlank.mk (List.replicate a one),
  Turing.ListBlank.mk (List.replicate b one)⟩⟩ →
nth_cfg (i + a * (2*a+2*b+1)) = some ⟨G, ⟨one,
  Turing.ListBlank.mk [],
  Turing.ListBlank.mk (List.replicate (b+a*2) one)⟩⟩
:= by
induction a with intros i b h
| zero => simp_all
| succ a ih =>
  apply copy_half_step at h
  apply ih at h
  ring_nf at *
  rw [← h]

lemma B_odd (n: ℕ) (h_odd : Odd n): ∀ (i: ℕ)(l r: List Γ),
nth_cfg i = some ⟨B, ⟨one,
  Turing.ListBlank.mk (zero :: l),
  Turing.ListBlank.mk (List.replicate n one ++ zero :: r)⟩⟩ →
∃ j>i, nth_cfg j = some ⟨C, ⟨zero,
  Turing.ListBlank.mk (List.replicate ((n+1)/2) one ++ l),
  Turing.ListBlank.mk (List.replicate (1+(n+1)/2) one ++ r)⟩⟩
:= by
induction' n using Nat.strongRecOn with n IH
intros i l r h
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
            use (8+i)
            simp [h]
  | succ n => ring_nf at h
              apply B_step at h
              specialize IH n (by omega)
              apply IH at h
              . obtain ⟨j, _, h⟩ := h
                use j
                constructor
                any_goals omega
                simp [h]
                ring_nf
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

lemma K_odd (n: ℕ) (h_odd : Odd n): ∀ (i: ℕ)(l r: List Γ),
nth_cfg i = some ⟨K, ⟨one,
  Turing.ListBlank.mk (zero :: l),
  Turing.ListBlank.mk (List.replicate n one ++ zero :: r)⟩⟩ →
∃ j>i, nth_cfg j = some ⟨C, ⟨zero,
  Turing.ListBlank.mk (List.replicate ((n+1)/2) one ++ l),
  Turing.ListBlank.mk (List.replicate (1+(n+1)/2) one ++ r)⟩⟩
:= by
intros i l r h
cases n with
| zero => simp at h_odd
| succ n => forward h
            apply recB at h
            forward h
            forward h
            rw [List.append_cons] at h
            rw [← List.replicate_one] at h
            rw [List.replicate_append_replicate] at h
            rw [List.replicate_succ] at h
            simp at h
            apply recD at h
            forward h
            forward h
            cases n with
            | zero => simp at h
                      forward h
                      use (8+i)
                      simp [h]
            | succ n => rw [List.replicate_succ] at h
                        simp at h
                        apply B_odd at h
                        . obtain ⟨j, _, h⟩ := h
                          use j
                          simp [h]
                          repeat any_goals apply And.intro
                          . omega
                          . rw [List.append_cons]
                            rw [← List.replicate_one]
                            rw [List.replicate_append_replicate]
                            have g : ((n+1) / 2 + 1) = ((n + 1 + 1+1) / 2) := by omega
                            rw [g]
                          . rw [List.append_cons]
                            rw [← List.replicate_one]
                            rw [List.replicate_append_replicate]
                            have g : (1+(n+1) / 2 + 1) = (1+(n + 1 + 1+1) / 2) := by omega
                            rw [g]
                        . obtain ⟨a, _⟩ := h_odd
                          cases a with
                          | zero => omega
                          | succ a => use a; omega

end Halt
