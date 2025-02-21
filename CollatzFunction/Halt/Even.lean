import CollatzFunction.Halt.TuringMachine10
import CollatzFunction.Halt.BStep

namespace Halt

open Lean Meta Elab Tactic Std Term TmState Γ

lemma B_even (n: ℕ) (h_even : Even n): ∀ (i: ℕ)(l r: List Γ),
nth_cfg i = some ⟨B, ⟨one,
  Turing.ListBlank.mk (zero :: l),
  Turing.ListBlank.mk (List.replicate n one ++ zero :: r)⟩⟩ →
∃ j>i, nth_cfg j = some ⟨A, ⟨zero,
  Turing.ListBlank.mk (List.replicate (1+n/2) one ++ l),
  Turing.ListBlank.mk (List.replicate (1+n/2) one ++ r)⟩⟩
:= by
induction' n using Nat.strongRecOn with n IH
intros i l r h
cases n with
| zero => simp
          forward h
          forward h
          forward h
          forward h
          use (4+i)
          simp [h]
| succ n => cases n with
  | zero => tauto
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
                have h : (2+n)/2 = n/2+1 := by omega
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
              . obtain ⟨k, h_even⟩ := h_even
                cases k with
                | zero => omega
                | succ k => use k; omega

lemma K_even (n: ℕ) (h_even : Even n) (i: ℕ) (l r: List Γ):
nth_cfg i = some ⟨K, ⟨one,
  Turing.ListBlank.mk (zero :: l),
  Turing.ListBlank.mk (List.replicate n one ++ zero :: r)⟩⟩ →
∃ j>i, nth_cfg j = some ⟨A, ⟨zero,
  Turing.ListBlank.mk (List.replicate (1+n/2) one ++ l),
  Turing.ListBlank.mk (List.replicate (1+n/2) one ++ r)⟩⟩
:= by
intros h
cases n with
| zero => forward h
          forward h
          forward h
          forward h
          use (4+i)
          simp [h]
| succ n => forward h
            apply recB at h
            forward h
            forward h
            rw [List.append_cons] at h
            rw [← List.replicate_one] at h
            rw [List.replicate_append_replicate] at h
            apply recD at h
            forward h
            forward h
            cases n with
            | zero => simp at h_even
            | succ n => rw [List.replicate_succ] at h
                        simp at h
                        apply B_even at h
                        . obtain ⟨j, _, h⟩ := h
                          use j
                          simp [h]
                          repeat any_goals apply And.intro
                          . omega
                          . rw [List.append_cons]
                            rw [← List.replicate_one]
                            rw [List.replicate_append_replicate]
                            have g : (1 + n / 2 + 1) = (1 + (n + 1 + 1) / 2) := by omega
                            rw [g]
                          . rw [List.append_cons]
                            rw [← List.replicate_one]
                            rw [List.replicate_append_replicate]
                            have g : (1 + n / 2 + 1) = (1 + (n + 1 + 1) / 2) := by omega
                            rw [g]
                        . obtain ⟨a, _⟩ := h_even
                          cases a with
                          | zero => omega
                          | succ a => use a; omega


end Halt
