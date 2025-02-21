import CollatzFunction.Halt.TuringMachine10
import CollatzFunction.Halt.Search0

namespace Halt

open Lean Meta Elab Tactic Std Term TmState Γ

lemma B_step (l r: List Γ) (n i: ℕ)
(h : nth_cfg i = some ⟨B, ⟨one,
  Turing.ListBlank.mk (List.cons zero l),
  Turing.ListBlank.mk (List.replicate (2+n) one ++ zero :: r)⟩⟩)
:
nth_cfg (9 + i + n * 2) = some ⟨B, ⟨one,
  Turing.ListBlank.mk (zero :: one :: l),
  Turing.ListBlank.mk (List.replicate n one ++ zero :: one :: r)⟩⟩
:= by
apply recB at h
forward h
have g : 2 + n = n + 2 := by omega
rw [g] at h
forward h
forward h
apply recD at h
forward h
forward h
rw [List.append_cons] at h
rw [← List.replicate_one] at h
rw [List.replicate_append_replicate] at h
simp only [ne_eq, List.replicate_succ_ne_nil, not_false_eq_true, List.tail_append_of_ne_nil, List.tail_replicate, Nat.add_one_sub_one] at h
rw [List.replicate_succ] at h
simp at h
rw [h]

lemma K_step (l r: List Γ) (n i: ℕ)
(h : nth_cfg i = some ⟨K, ⟨one,
  Turing.ListBlank.mk (List.cons zero l),
  Turing.ListBlank.mk (List.replicate (2+n) one ++ zero :: r)⟩⟩)
:
nth_cfg (9 + i + n * 2) = some ⟨B, ⟨one,
  Turing.ListBlank.mk (zero :: one :: l),
  Turing.ListBlank.mk (List.replicate n one ++ zero :: one :: r)⟩⟩
:= by
forward h
have k : 2+n = n+1+1 := by omega
rw [k] at h
rw [List.replicate_succ] at h
simp at h
apply recB at h
forward h
forward h
rw [add_comm 1 n] at h
rw [List.replicate_succ] at h
simp at h
rw [List.append_cons] at h
rw [← List.replicate_one] at h
rw [List.replicate_append_replicate] at h
apply recD at h
forward h
forward h
exact h

end Halt
