import CollatzFunction.Halt.TuringMachine10
import CollatzFunction.Halt.Search0

namespace Halt

open Lean Meta Elab Tactic Std Term TmState Γ

theorem lemma_G_to_H (r: List Γ)(r1: ℕ)(i : ℕ)(l: List Γ)
(h :
nth_cfg i = some ⟨G, ⟨Γ.one,
  Turing.ListBlank.mk l,
  Turing.ListBlank.mk (List.replicate r1 Γ.one ++ List.cons Γ.zero r)⟩⟩) :
nth_cfg (i+r1+1) = some ⟨H, ⟨Γ.zero,
  Turing.ListBlank.mk (List.replicate r1 Γ.one ++ List.cons Γ.zero l),
  Turing.ListBlank.mk r⟩⟩
:= by
forward h
cases r1 with
| zero => ring_nf at *
          simp [h]
| succ r1 => apply recH at h
             ring_nf at *
             simp [h]

theorem lemma_H_to_J (r: List Γ)(r1: ℕ)(i : ℕ)(l: List Γ)
(h :
nth_cfg i = some ⟨H, ⟨Γ.zero,
  Turing.ListBlank.mk (List.replicate r1 Γ.one ++ List.cons Γ.zero r),
  Turing.ListBlank.mk l⟩⟩) :
nth_cfg (i+r1+1) = some ⟨J, ⟨Γ.zero,
  Turing.ListBlank.mk r,
  Turing.ListBlank.mk (List.replicate r1 Γ.one ++ List.cons Γ.one l)⟩⟩
:= by
forward h
cases r1 with
| zero => ring_nf at *
          simp [h]
| succ r1 => apply recJ at h
             ring_nf at *
             simp [h]

end Halt
