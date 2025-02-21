import CollatzFunction.NonHalt.TuringMachine9
import CollatzFunction.NonHalt.Even
import CollatzFunction.NonHalt.Odd
import CollatzFunction.NonHalt.Search0
import CollatzFunction.NonHalt.Search1
import CollatzFunction.NonHalt.Zeroing
import CollatzFunction.NonHalt.Transition
import CollatzFunction.Collatz
import CollatzFunction.ListBlank

namespace NonHalt

open Lean Meta Elab Tactic Std Term TmState Γ

-- if n ≥ 1, n -> collatz n
theorem F_collatz (n: ℕ) (_ : n ≥ 1) (i: ℕ)
(h : nth_cfg i = some ⟨F, ⟨one,
  Turing.ListBlank.mk [],
  Turing.ListBlank.mk (List.replicate (n-1) one)⟩⟩) :
∃ j>i, nth_cfg j = some ⟨F, ⟨one,
  Turing.ListBlank.mk [],
  Turing.ListBlank.mk (List.replicate ((collatz n)-1) one)⟩⟩
:= by
cases n with
| zero => omega
| succ n => forward h
            cases n with
            | zero => simp
                      forward h
                      unfold collatz
                      simp
                      forward h
                      forward h
                      use (4+i)
                      simp [h]
                      simp! [Turing.ListBlank.mk]
                      rw [Quotient.eq'']
                      right
                      use 1
                      tauto
            | succ n =>
  rw [List.replicate_succ] at h
  simp at h
  unfold collatz
  split_ifs <;> rename_i g
  . rw [← (ListBlank_empty_eq_single_zero (List.replicate n one))] at h
    apply B_even at h
    obtain ⟨j, _, h⟩ := h
    forward h
    rw [add_comm 1 (n/2)] at h
    rw [List.replicate_succ] at h
    simp at h
    rw [← (ListBlank_empty_eq_single_zero (List.replicate (n/2) one))] at h
    apply E_zeroing at h
    forward h
    apply recF at h
    forward h
    use (5 + j + n / 2 * 2)
    ring_nf at *
    simp [h]
    repeat any_goals apply And.intro
    . omega
    . rw [← List.replicate_succ']
      ring_nf
      simp! [Turing.ListBlank.mk]
      rw [Quotient.eq'']
      right
      use 3 + n/2
      rw [← List.replicate_succ]
      rw [← List.replicate_succ]
      simp
      ring_nf
      tauto
    . rw [← Nat.even_iff] at g
      obtain ⟨a, g⟩ := g
      cases a with
      | zero => omega
      | succ a => use a; omega
  . cases n with
    | zero => omega
    | succ n =>
      rw [← (ListBlank_empty_eq_single_zero (List.replicate (n+1) one))] at h
      apply B_odd at h
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

end NonHalt
