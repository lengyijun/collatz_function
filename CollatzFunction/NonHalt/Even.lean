import CollatzFunction.NonHalt.TuringMachine9
import CollatzFunction.NonHalt.BStep

namespace NonHalt

open Lean Meta Elab Tactic Std Term TmState Γ

lemma B_even (n: ℕ) (h_even : Even n): ∀ (i: ℕ)(l r: List Γ)(init_cfg: Cfg),
nth_cfg init_cfg i =  ⟨B, ⟨one,
  Turing.ListBlank.mk (zero :: l),
  Turing.ListBlank.mk (List.replicate n one ++ zero :: r)⟩⟩ →
∃ j>i, nth_cfg init_cfg j =  ⟨A, ⟨zero,
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

end NonHalt
