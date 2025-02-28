import CollatzFunction.NonHalt.TuringMachine9
import CollatzFunction.NonHalt.Search0

namespace NonHalt

open Lean Meta Elab Tactic Std Term TmState Γ

private lemma G_to_H (r: List Γ)(r1: ℕ)(i : ℕ)(l: List Γ)(init_cfg: Cfg)
(h :
nth_cfg init_cfg i =  ⟨G, ⟨Γ.one,
  Turing.ListBlank.mk l,
  Turing.ListBlank.mk (List.replicate r1 Γ.one ++ List.cons Γ.zero r)⟩⟩) :
nth_cfg init_cfg (i+r1+1) =  ⟨H, ⟨Γ.zero,
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

private lemma H_to_J (r: List Γ)(r1: ℕ)(i : ℕ)(l: List Γ)(init_cfg: Cfg)
(h :
nth_cfg init_cfg i =  ⟨H, ⟨Γ.zero,
  Turing.ListBlank.mk (List.replicate r1 Γ.one ++ List.cons Γ.zero r),
  Turing.ListBlank.mk l⟩⟩) :
nth_cfg init_cfg (i+r1+1) =  ⟨J, ⟨Γ.zero,
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

theorem G_to_J (r: List Γ)(r1: ℕ)(i : ℕ)(l: List Γ)(init_cfg: Cfg)
(h :
nth_cfg init_cfg i = ⟨G, ⟨Γ.one,
  Turing.ListBlank.mk l,
  Turing.ListBlank.mk (List.replicate r1 Γ.one ++ List.cons Γ.zero r)⟩⟩) :
nth_cfg init_cfg (2+i+r1*2) = ⟨J, ⟨Γ.zero,
  Turing.ListBlank.mk l,
  Turing.ListBlank.mk (List.replicate r1 Γ.one ++ List.cons Γ.one r)⟩⟩
:= by
apply G_to_H at h
apply H_to_J at h
ring_nf at h
simp [h]

end NonHalt
