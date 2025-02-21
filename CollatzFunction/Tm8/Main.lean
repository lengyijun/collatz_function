import CollatzFunction.Tm8.TuringMachine8
import CollatzFunction.Tm8.Even
import CollatzFunction.Tm8.Odd
import CollatzFunction.Tm8.Search0
import CollatzFunction.Tm8.Transition
import CollatzFunction.Tm8.Representation
import CollatzFunction.Collatz
import CollatzFunction.ListBlank

namespace Tm8

open Lean Meta Elab Tactic Std Term TmState Γ

-- n -> collatz n
theorem G_collatz (n i: ℕ) (init_cfg: Cfg)
(h: nth_cfg_is_n i n init_cfg) :
∃ j>i, nth_cfg_is_n j (collatz n) init_cfg
:= by
obtain ⟨l, h⟩ := h
-- somehow surprise, the proof of `inl h` and `inr h` are the same
cases h with
| inl h => cases n with
  | zero => forward h
            forward h
            use (2+i)
            constructor
            any_goals omega
            use l
            left
            unfold collatz
            simp [h]
            simp! [Turing.ListBlank.mk]
            rw [Quotient.eq'']
            right
            use 1
            tauto
  | succ n => forward h
              cases n with
    | zero => simp at h
              forward h
              forward h
              forward h
              use (4+i)
              constructor
              any_goals omega
              use l
              right
              unfold collatz
              simp [h]
    | succ n => forward h
                unfold collatz
                split_ifs <;> rename_i g
                . rw [← (ListBlank_empty_eq_single_zero (List.replicate n one))] at h
                  apply B_even at h
                  forward h
                  rw [add_comm 1 (n/2)] at h
                  rw [List.replicate_succ] at h
                  simp at h
                  forward h
                  use (8 + i + n ^ 2 / 2 + n * 7 / 2)
                  constructor
                  any_goals omega
                  use (List.replicate (n / 2) one ++ zero :: zero :: l)
                  left
                  simp [h]
                  rw [← List.replicate_succ]
                  apply congr
                  any_goals rfl
                  apply congr
                  any_goals rfl
                  apply congr
                  any_goals rfl
                  omega
                  rw [← Nat.even_iff] at g
                  obtain ⟨a, g⟩ := g
                  cases a with
                  | zero => omega
                  | succ a => use a; omega
                . rw [← (ListBlank_empty_eq_single_zero (List.replicate n one))] at h
                  apply B_odd at h
                  forward h
                  cases n with
                  | zero => omega
                  | succ n =>
                    ring_nf at h
                    have g : (2+n)/2 = n/2 + 1:= by omega
                    rw [g] at h
                    rw [List.replicate_succ] at h
                    simp at h
                    rw [← List.replicate_succ] at h
                    apply copy_half at h
                    rw [← (ListBlank_empty_eq_single_zero (List.replicate _ one))] at h
                    apply G_to_J at h
                    forward h
                    use (16 + i + (8 + n * 9 + n ^ 2) / 2 + n / 2 * 13 + (n / 2) ^ 2 * 4)
                    constructor
                    any_goals omega
                    use l
                    right
                    simp [h]
                    apply congr
                    any_goals rfl
                    rw [← List.replicate_one]
                    rw [List.replicate_append_replicate]
                    rw [← List.replicate_succ]
                    apply congr
                    any_goals rfl
                    apply congr
                    any_goals rfl
                    omega
                  have g : (n+2) % 2 = 1 := by omega
                  rw [← Nat.odd_iff] at g
                  obtain ⟨a, g⟩ := g
                  cases a with
                  | zero => omega
                  | succ a => use a; omega
| inr h => cases n with
  | zero => forward h
            forward h
            use (2+i)
            constructor
            any_goals omega
            use l
            left
            unfold collatz
            simp [h]
            simp! [Turing.ListBlank.mk]
            rw [Quotient.eq'']
            right
            use 1
            tauto
  | succ n => forward h
              cases n with
    | zero => simp at h
              forward h
              forward h
              forward h
              use (4+i)
              constructor
              any_goals omega
              use l
              right
              unfold collatz
              simp [h]
    | succ n => forward h
                unfold collatz
                split_ifs <;> rename_i g
                . rw [← (ListBlank_empty_eq_single_zero (List.replicate n one))] at h
                  apply B_even at h
                  obtain ⟨j, _, h⟩ := h
                  forward h
                  rw [add_comm 1 (n/2)] at h
                  rw [List.replicate_succ] at h
                  simp at h
                  forward h
                  use (2+j)
                  constructor
                  any_goals omega
                  use (List.replicate (n / 2) one ++ zero :: zero :: l)
                  left
                  simp [h]
                  rw [← List.replicate_succ]
                  apply congr
                  any_goals rfl
                  apply congr
                  any_goals rfl
                  apply congr
                  any_goals rfl
                  omega
                  rw [← Nat.even_iff] at g
                  obtain ⟨a, g⟩ := g
                  cases a with
                  | zero => omega
                  | succ a => use a; omega
                . rw [← (ListBlank_empty_eq_single_zero (List.replicate n one))] at h
                  apply B_odd at h
                  obtain ⟨j, _, h⟩ := h
                  forward h
                  cases n with
                  | zero => omega
                  | succ n =>
                    ring_nf at h
                    have g : (2+n)/2 = n/2 + 1:= by omega
                    rw [g] at h
                    rw [List.replicate_succ] at h
                    simp at h
                    rw [← List.replicate_succ] at h
                    apply copy_half at h
                    rw [← (ListBlank_empty_eq_single_zero (List.replicate _ one))] at h
                    apply G_to_J at h
                    forward h
                    use (10 + j + n / 2 * 13 + (n / 2) ^ 2 * 4)
                    constructor
                    any_goals omega
                    use l
                    right
                    simp [h]
                    apply congr
                    any_goals rfl
                    rw [← List.replicate_one]
                    rw [List.replicate_append_replicate]
                    rw [← List.replicate_succ]
                    apply congr
                    any_goals rfl
                    apply congr
                    any_goals rfl
                    omega
                  have g : (n+2) % 2 = 1 := by omega
                  rw [← Nat.odd_iff] at g
                  obtain ⟨a, g⟩ := g
                  cases a with
                  | zero => omega
                  | succ a => use a; omega

end Tm8
