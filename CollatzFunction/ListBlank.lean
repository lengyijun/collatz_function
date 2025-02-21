-- some helper of ListBlank
import Mathlib.Computability.TuringMachine
import CollatzFunction.Basic

def to_list_rev (l : Turing.ListBlank Γ) : List Γ := by
  apply l.liftOn (fun l ↦ l.reverse.dropWhile (fun c ↦ c == Γ.zero))
  rintro a _ ⟨i, rfl⟩
  cases a <;> simp
  . tauto
  . induction i
    . tauto
    . simp [*]
      tauto

def to_list (l : Turing.ListBlank Γ) : List Γ := l |> to_list_rev |> List.reverse

theorem to_list_rev_rfl (l : List Γ) : to_list_rev (Turing.ListBlank.mk l) = l.reverse.dropWhile (fun c ↦ c == Γ.zero) := rfl

theorem to_list_rev_one (l : Turing.ListBlank Γ) : to_list_rev (l.cons Γ.one) = (to_list_rev l) ++ [Γ.one] := by
  refine l.inductionOn fun l ↦ ?_
  suffices to_list_rev ((Turing.ListBlank.mk l).cons Γ.one) = (to_list_rev (Turing.ListBlank.mk l)) ++ [Γ.one] by exact this
  simp [Turing.ListBlank.cons_mk, to_list_rev_rfl, to_list_rev_rfl, List.dropWhile_append]


open Γ

theorem  ListBlank_empty_eq_single_zero: ∀ l, Turing.ListBlank.mk (l ++ [zero]) = Turing.ListBlank.mk l := by
  intros l
  simp! [Turing.ListBlank.mk]
  rw [Quotient.eq'']
  right
  use 1
  tauto
