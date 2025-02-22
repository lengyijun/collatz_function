-- deprecated F_collatz is better
-- if n >= 3, n -> collatz n
lemma B_collatz (n: ℕ) (_ : n > 0) (i: ℕ)
(h : nth_cfg i =  ⟨B, ⟨one,
  Turing.ListBlank.mk [],
  Turing.ListBlank.mk (List.replicate n one)⟩⟩) :
∃ j>i, nth_cfg j =  ⟨B, ⟨one,
  Turing.ListBlank.mk [],
  Turing.ListBlank.mk (List.replicate ((collatz (n+2))-2) one)⟩⟩
:= by
unfold collatz
split_ifs <;> rename_i g
. rw [← ListBlank_empty_eq_single_zero []] at h
  simp at h
  rw [← (ListBlank_empty_eq_single_zero (List.replicate n one))] at h
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
  forward h
  use (6 + j + n / 2 * 2)
  simp [h]
  repeat any_goals apply And.intro
  . omega
  . cases n with
    | zero => omega
    | succ n => cases n with
      | zero => omega
      | succ n => ring_nf
                  have h : (2+n)/2 = n/2 + 1:= by omega
                  rw [h]
                  rw [List.replicate_succ]
                  simp
  . simp! [Turing.ListBlank.mk]
    rw [Quotient.eq'']
    right
    use (n/2+1+1+1+1)
    rw [← List.cons_append]
    rw [← List.cons_append]
    rw [← List.cons_append]
    rw [← List.replicate_succ]
    rw [← List.replicate_succ]
    rw [← List.replicate_succ]
    rw [List.append_cons]
    rw [← List.replicate_succ']
    simp
    tauto
  . rw [← Nat.even_iff] at g
    obtain ⟨a, g⟩ := g
    cases a with
    | zero => omega
    | succ a => use a; omega
. rw [← ListBlank_empty_eq_single_zero []] at h
  simp at h
  rw [← (ListBlank_empty_eq_single_zero (List.replicate n one))] at h
  apply B_odd at h
  obtain ⟨j, _, h⟩ := h
  forward h
  cases n with
  | zero => omega
  | succ n =>
    ring_nf at h
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
    forward h
    rw [← List.replicate_succ'] at h
    rw [List.replicate_succ] at h
    simp at h
    rw [← List.replicate_succ'] at h
    ring_nf at h
    use (12 + j + n / 2 * 13 + (n / 2) ^ 2 * 4)
    simp [h]
    repeat any_goals apply And.intro
    . omega
    . simp! [Turing.ListBlank.mk]
      rw [Quotient.eq'']
      right
      use 2
      tauto
    . ring_nf
      apply congr
      any_goals rfl
      apply congr
      any_goals rfl
      apply congr
      any_goals rfl
      omega
  . have g : (n+2) % 2 = 1 := by omega
    rw [← Nat.odd_iff] at g
    obtain ⟨a, g⟩ := g
    cases a with
    | zero => omega
    | succ a => use a; omega
