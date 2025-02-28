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
    forward h
    rw [add_comm 1 (n/2)] at h
    rw [List.replicate_succ] at h
    simp at h
    rw [← (ListBlank_empty_eq_single_zero (List.replicate (n/2) one))] at h
    apply E_zeroing at h
    forward h
    apply recF at h
    forward h
    use (10 + i + n ^ 2 / 2 + n * 7 / 2 + n / 2 * 2)
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
    . ring_nf
      apply congr
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
  . cases n with
    | zero => omega
    | succ n =>
      rw [← (ListBlank_empty_eq_single_zero (List.replicate (n+1) one))] at h
      apply B_odd at h
      forward h
      have k : (2+n)/2 = n/2 + 1:= by omega
      rw [k] at h
      rw [List.replicate_succ] at h
      simp at h
      rw [← List.replicate_succ] at h
      apply copy_half at h
      rw [← (ListBlank_empty_eq_single_zero (List.replicate _ one))] at h
      apply G_to_J at h
      forward h
      forward h
      use (16 + i + (8 + n * 9 + n ^ 2) / 2 + n / 2 * 13 + (n / 2) ^ 2 * 4)
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
