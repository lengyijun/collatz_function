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

lemma F_odd (n i: ℕ) (h_odd: Odd n) (init_cfg: Cfg)
(h : nth_cfg init_cfg i =  ⟨F, ⟨one,
  Turing.ListBlank.mk [],
  Turing.ListBlank.mk (List.replicate (n-1) one)⟩⟩) :
nth_cfg init_cfg (i+(3 * n^2+4*n+1)/2) =  ⟨F, ⟨one,
  Turing.ListBlank.mk [],
  Turing.ListBlank.mk (List.replicate ((collatz n)-1) one)⟩⟩
:= by
cases n with
| zero => ring_nf at *; tauto
| succ n => forward h
            cases n with
            | zero => ring_nf at *
                      forward h
                      forward h
                      forward h
                      simp [h]
                      simp [collatz]
                      simp! [Turing.ListBlank.mk]
                      rw [Quotient.eq'']
                      right
                      use 1
                      tauto
            | succ n => obtain ⟨k, h_odd⟩ := h_odd
                        cases k with
                        | zero => omega
                        | succ k =>
                          have h_odd : n = 2 * k+1 := by omega
                          subst n
                          rw [← (ListBlank_empty_eq_single_zero (List.replicate _ one))] at h
                          apply B_odd at h
                          . ring_nf at *
                            forward h
                            have g : (1 +(2+k*2-1)) /2 = k + 1:= by omega
                            rw [g] at h
                            rw [List.replicate_succ] at h
                            simp at h
                            rw [← List.replicate_succ] at h
                            apply copy_half at h
                            rw [← (ListBlank_empty_eq_single_zero (List.replicate _ one))] at h
                            apply G_to_J at h
                            forward h
                            forward h
                            simp [collatz]
                            ring_nf at *
                            have g : i + (40 + k * 44 + k ^ 2 * 12) / 2 = 20 + 22 * k + 6 * k ^ 2 + i := by omega
                            rw [g]
                            have g :  2+k*2-1 = k*2 +1 := by omega
                            rw [g] at h
                            have g : (k * 2 + 1) ^ 2 = 4 * k + 4 * k ^ 2 + 1 := by ring_nf
                            have g : ((k * 2 + 1) * 7 + (k * 2 + 1) ^ 2) / 2 = 4 + 9 * k + 2 * k ^ 2 := by omega
                            have g : 16 + i + k * 13 + k ^ 2 * 4 + ((k * 2 + 1) * 7 + (k * 2 + 1) ^ 2) / 2 = 20 + 22 * k + 6 * k ^ 2 + i := by omega
                            rw [← g]
                            simp [h]
                            constructor
                            . simp! [Turing.ListBlank.mk]
                              rw [Quotient.eq'']
                              right
                              use 1
                              tauto
                            . rw [← List.replicate_one]
                              rw [List.replicate_append_replicate]
                              apply congr
                              any_goals rfl
                              apply congr
                              any_goals rfl
                              apply congr
                              any_goals rfl
                              omega
                          . use k; omega


variable {a b c : ℕ}

lemma F_even (n i: ℕ)  (_ : n ≥ 1) (h_even: Even n) (init_cfg: Cfg)
(h : nth_cfg init_cfg i =  ⟨F, ⟨one,
  Turing.ListBlank.mk [],
  Turing.ListBlank.mk (List.replicate (n-1) one)⟩⟩) :
nth_cfg init_cfg (i+(n^2+5*n)/2+3) =  ⟨F, ⟨one,
  Turing.ListBlank.mk [],
  Turing.ListBlank.mk (List.replicate ((collatz n)-1) one)⟩⟩
:= by
cases n with
| zero => omega
| succ n => cases n with
            | zero => tauto
            | succ n => obtain ⟨k, h_even⟩ := h_even
                        cases k with
                        | zero => omega
                        | succ k =>
                          have h_even : n = 2 * k := by omega
                          subst n
                          forward h
                          rw [add_comm 1 (k*2)] at h
                          rw [List.replicate_succ] at h
                          simp at h
                          rw [← (ListBlank_empty_eq_single_zero (List.replicate _ one))] at h
                          apply B_even at h
                          . forward h
                            rw [add_comm 1 k] at h
                            rw [List.replicate_succ] at h
                            simp at h
                            rw [← (ListBlank_empty_eq_single_zero (List.replicate _ one))] at h
                            apply E_zeroing at h
                            forward h
                            apply recF at h
                            forward h
                            simp [collatz]
                            ring_nf at *
                            simp
                            have g : k * 14 / 2  = k  * 7 := by omega
                            rw [g] at h
                            have g : (14 + k * 18 + k ^ 2 * 4) / 2 = 7 + k * 9 + k ^ 2 * 2 := by omega
                            rw [g]
                            have g : k ^ 2 * 4 / 2  = k ^ 2 * 2 := by omega
                            rw [g] at h
                            ring_nf at *
                            simp [h]
                            simp! [Turing.ListBlank.mk]
                            rw [Quotient.eq'']
                            right
                            use (3+k)
                            simp
                            rw [← List.replicate_one]
                            rw [List.replicate_append_replicate]
                            rw [← List.replicate_succ]
                            rw [← List.replicate_succ]
                            ring_nf
                            tauto
                          . use k; omega

-- if n ≥ 1, n -> collatz n
theorem F_collatz (n: ℕ) (_ : n ≥ 1) (i: ℕ) (init_cfg: Cfg)
(h : nth_cfg init_cfg i =  ⟨F, ⟨one,
  Turing.ListBlank.mk [],
  Turing.ListBlank.mk (List.replicate (n-1) one)⟩⟩) :
∃ j>i, nth_cfg init_cfg j =  ⟨F, ⟨one,
  Turing.ListBlank.mk [],
  Turing.ListBlank.mk (List.replicate ((collatz n)-1) one)⟩⟩
:= by
cases (Nat.even_or_odd n) with
| inl _ =>  apply F_even at h
            any_goals assumption
            use (i + (n ^ 2 + 5 * n) / 2 + 3)
            constructor
            . omega
            . simp [h]
| inr _ =>  apply F_odd at h
            any_goals assumption
            use (i + (3 * n ^ 2 + 4 * n + 1) / 2)
            constructor
            . cases n with
              | zero => tauto
              | succ n => omega
            . simp [h]

end NonHalt
