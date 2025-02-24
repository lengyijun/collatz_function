import CollatzFunction.NonHalt.TuringMachine9
import CollatzFunction.NonHalt.Search0

namespace NonHalt

open Lean Meta Elab Tactic Std Term TmState Γ

lemma B_step (l r: List Γ) (n i: ℕ) (init_cfg: Cfg)
(h : nth_cfg init_cfg i =  ⟨B, ⟨one,
  Turing.ListBlank.mk (List.cons zero l),
  Turing.ListBlank.mk (List.replicate (2+n) one ++ zero :: r)⟩⟩)
:
nth_cfg init_cfg (9 + i + n * 2) =  ⟨B, ⟨one,
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

end NonHalt
