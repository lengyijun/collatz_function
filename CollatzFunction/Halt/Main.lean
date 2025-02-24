import CollatzFunction.Halt.TuringMachine10
import CollatzFunction.Halt.Even
import CollatzFunction.Halt.Odd
import CollatzFunction.Halt.Search0
import CollatzFunction.Halt.Search1
import CollatzFunction.Halt.Zeroing
import CollatzFunction.Halt.Transition
import CollatzFunction.Collatz
import CollatzFunction.ListBlank

namespace Halt

open Lean Meta Elab Tactic Std Term TmState Γ

-- if n ≥ 2, n -> collatz n
theorem F_collatz (n: ℕ) (_ : n ≥ 2) (i: ℕ) (init_cfg: Cfg)
(h : nth_cfg init_cfg i = some ⟨F, ⟨one,
  Turing.ListBlank.mk [],
  Turing.ListBlank.mk (List.replicate (n-1) one)⟩⟩) :
∃ j>i, nth_cfg init_cfg j = some ⟨F, ⟨one,
  Turing.ListBlank.mk [],
  Turing.ListBlank.mk (List.replicate ((collatz n)-1) one)⟩⟩
:= by
cases n with
| zero => omega
| succ n => forward h
            cases n with
            | zero => omega
            | succ n => cases n with
              | zero => simp
                        forward h
                        unfold collatz
                        simp
                        forward h
                        forward h
                        forward h
                        forward h
                        forward h
                        forward h
                        forward h
                        forward h
                        use (10+i)
                        simp [h]
                        simp! [Turing.ListBlank.mk]
                        rw [Quotient.eq'']
                        right
                        use 3
                        tauto
              | succ n =>
  rw [List.replicate_succ] at h
  simp at h
  unfold collatz
  split_ifs <;> rename_i g
  . rw [← (ListBlank_empty_eq_single_zero (List.replicate _ one))] at h
    apply K_even at h
    obtain ⟨j, _, h⟩ := h
    forward h
    rw [add_comm 1 ((1+n)/2)] at h
    rw [List.replicate_succ] at h
    simp at h
    rw [← (ListBlank_empty_eq_single_zero (List.replicate _ one))] at h
    apply E_zeroing at h
    forward h
    apply recF at h
    forward h
    use (5 + j + (1+n) / 2 * 2)
    ring_nf at *
    simp [h]
    repeat any_goals apply And.intro
    . omega
    . rw [← List.replicate_succ']
      ring_nf
      simp! [Turing.ListBlank.mk]
      rw [Quotient.eq'']
      right
      use 3 + (1+n)/2
      rw [← List.replicate_succ]
      rw [← List.replicate_succ]
      simp
      ring_nf
      tauto
    . apply congr
      any_goals rfl
      apply congr
      any_goals rfl
      apply congr
      any_goals rfl
      omega
    . rw [← Nat.even_iff] at g
      obtain ⟨a, g⟩ := g
      cases a with
      | zero => omega
      | succ a => use a; omega
  . rw [← (ListBlank_empty_eq_single_zero (List.replicate (n+1) one))] at h
    apply K_odd at h
    obtain ⟨j, _, h⟩ := h
    forward h
    have k : (2+n)/2 = n/2 + 1:= by omega
    rw [k] at h
    rw [List.replicate_succ] at h
    simp at h
    rw [← List.replicate_succ] at h
    apply copy_half at h
    rw [← (ListBlank_empty_eq_single_zero (List.replicate _ one))] at h
    apply lemma_G_to_H at h
    apply lemma_H_to_J at h
    forward h
    forward h
    use (11 + j + n / 2 * 13 + (n / 2) ^ 2 * 4)
    simp [h]
    repeat any_goals apply And.intro
    . omega
    . simp! [Turing.ListBlank.mk]
      rw [Quotient.eq'']
      right
      use 1
      tauto
    . apply congr
      any_goals rfl
      rw [← List.replicate_succ']
      apply congr
      any_goals rfl
      apply congr
      any_goals rfl
      omega
    . have g : (n+3) % 2 = 1 := by omega
      rw [← Nat.odd_iff] at g
      obtain ⟨a, g⟩ := g
      cases a with
      | zero => omega
      | succ a => use a; omega

end Halt
