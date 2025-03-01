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

lemma G_even (n i: ℕ) (h_even: Even n) (init_cfg: Cfg)
(h: nth_cfg_is_n i n init_cfg) :
nth_cfg_is_n (i+(n^2+3*n)/2+3) (collatz n) init_cfg
:= by
obtain ⟨l, h⟩ := h
match n with
| 0 =>  use (zero :: l)
        unfold collatz
        simp
        forward h
        forward h
        forward h
        ring_nf at *
        simp [h]
| 1 => tauto
| Nat.succ (Nat.succ n) =>
    obtain ⟨k, h_even⟩ := h_even
    cases k with
    | zero => omega
    | succ k =>
      have h_even : n = 2 * k := by omega
      subst n
      forward h
      forward h
      rw [← (ListBlank_empty_eq_single_zero (List.replicate _ one))] at h
      apply B_even at h
      . forward h
        rw [add_comm 1] at h
        rw [List.replicate_succ] at h
        simp at h
        forward h
        ring_nf at *
        have g : 3 + i + ((k * 2).succ.succ * 3 + (k * 2).succ.succ ^ 2) / 2 = 8 + i + k ^ 2 * 4 / 2 + k * 14 / 2 := by
          simp
          ring_nf
          calc
            _ = 3 + i + 5 + k * 7 + 2 * k ^ 2 := by omega
            _ = 8 + i + k ^ 2 * 2 + k * 7 := by ring_nf
            _ = _  := by omega
        rw [g]
        use (List.replicate k one ++ zero :: zero :: l)
        simp [h]
        simp [collatz]
        ring_nf
        simp
        rw [List.replicate_succ]
      . use k; omega


lemma G_odd (n i: ℕ) (h_odd: Odd n) (init_cfg: Cfg)
(h: nth_cfg_is_n i n init_cfg) :
nth_cfg_is_n (i+(3 * n^2+4*n+1)/2) (collatz n) init_cfg
:= by
obtain ⟨l, h⟩ := h
match n with
| 0 => tauto
| 1 =>  forward h
        ring_nf at *
        forward h
        forward h
        forward h
        use l
        simp [h]
        simp [collatz]
| Nat.succ (Nat.succ n) =>
    forward h
    obtain ⟨k, h_odd⟩ := h_odd
    cases k with
    | zero => omega
    | succ k =>
      have h_odd : n = 2 * k+1 := by omega
      subst n
      forward h
      rw [← List.replicate_succ] at h
      rw [← (ListBlank_empty_eq_single_zero (List.replicate _ one))] at h
      apply B_odd at h
      . forward h
        have g : (2 +k*2) /2 = k + 1:= by omega
        rw [g] at h
        rw [List.replicate_succ] at h
        simp at h
        rw [← List.replicate_succ] at h
        apply copy_half at h
        rw [← (ListBlank_empty_eq_single_zero (List.replicate _ one))] at h
        apply G_to_J at h
        forward h
        ring_nf at *
        have g : i + (1 + (1 + k * 2).succ.succ * 4 + (1 + k * 2).succ.succ ^ 2 * 3) / 2 = 16 + i + k * 13 + k ^ 2 * 4 + (8 + k * 18 + k ^ 2 * 4) / 2 := by
          simp
          ring_nf
          calc
            _ = i + 20 + 22 * k + 6 * k^2 := by omega
            _ = 16 + i + k * 13 + k ^ 2 * 4 + 4 + k * 9 + k ^ 2 * 2 := by ring_nf
            _ = _ := by omega
        rw [g]
        use l
        simp [h]
        simp [collatz]
        ring_nf
        simp
        rw [← List.replicate_one]
        rw [List.replicate_append_replicate]
        rw [← List.replicate_succ]
        apply congr
        any_goals rfl
        apply congr
        any_goals rfl
        apply congr
        any_goals rfl
        omega
      . use k; omega

-- n -> collatz n
theorem G_collatz (n i: ℕ) (init_cfg: Cfg)
(h: nth_cfg_is_n i n init_cfg) :
∃ j>i, nth_cfg_is_n j (collatz n) init_cfg
:= by
cases (Nat.even_or_odd n) with
| inl _ =>  apply G_even at h
            any_goals assumption
            use (i + (n ^ 2 + 3 * n) / 2 + 3)
            constructor
            . omega
            . simp [h]
| inr _ =>  apply G_odd at h
            any_goals assumption
            use (i + (3 * n ^ 2 + 4 * n + 1) / 2)
            constructor
            . cases n with
              | zero => tauto
              | succ n => omega
            . simp [h]

end Tm8
