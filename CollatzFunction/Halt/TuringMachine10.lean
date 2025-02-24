-- inspired by https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Computability/TuringMachine.lean
import Mathlib.Computability.TuringMachine
import Mathlib.Tactic.Ring.RingNF
import CollatzFunction.Basic
import CollatzFunction.Format
import CollatzFunction.ListBlank

namespace Halt

inductive TmState where
| A : TmState
| B : TmState
| C : TmState
| D : TmState
| E : TmState
| F : TmState
| G : TmState
| H : TmState
| J : TmState
| K : TmState
 deriving BEq

open Lean Meta Elab Tactic Std Term TmState

def TmState.toString : TmState → String
| A => s!"A"
| B => s!"B"
| C => s!"C"
| D => s!"D"
| E => s!"E"
| F => s!"F"
| G => s!"G"
| H => s!"H"
| J => s!"J"
| K => s!"K"

instance : ToString TmState where
  toString := TmState.toString


def Machine := TmState → Γ → Option (TmState × Stmt)

structure Cfg where
  /-- The current machine state. -/
  q : TmState
  /-- The current state of the tape: current symbol, left and right parts. -/
  tape : Turing.Tape Γ


instance : ToString Cfg where
  toString := fun ⟨q, ⟨head, l, r⟩⟩ ↦
    let l : String := join ((to_list_rev l).map ToString.toString)
    let r : String := join ((to_list r).map ToString.toString)
    let s : String := if l == "" then s!"[{head}]{r}"
                                 else s!" {l}[{head}]{r}"
    s!"{q}   {s}"

/-- The initial configuration. -/
def init (l : List Γ) : Cfg := ⟨TmState.F, Turing.Tape.mk₁ l⟩

/-- Execution semantics of the Turing machine. -/
def step (M : Machine) : Cfg → Option Cfg :=
  fun ⟨q, T⟩ ↦ (M q T.head).map fun ⟨q', a⟩ ↦ ⟨q', (T.write a.write).move a.move⟩


def machine : Machine
| A, Γ.zero => some ⟨E, ⟨Turing.Dir.left, Γ.zero⟩⟩
| A, Γ.one => some ⟨B, ⟨Turing.Dir.right, Γ.zero⟩⟩
| B, Γ.zero => some ⟨C, ⟨Turing.Dir.left, Γ.one⟩⟩
| B, Γ.one => some ⟨B, ⟨Turing.Dir.right, Γ.one⟩⟩
| C, Γ.zero => some ⟨G, ⟨Turing.Dir.left, Γ.one⟩⟩
| C, Γ.one => some ⟨D, ⟨Turing.Dir.left, Γ.zero⟩⟩
| D, Γ.zero => some ⟨A, ⟨Turing.Dir.right, Γ.one⟩⟩
| D, Γ.one => some ⟨D, ⟨Turing.Dir.left, Γ.one⟩⟩
| E, Γ.zero => some ⟨F, ⟨Turing.Dir.right, Γ.zero⟩⟩
| E, Γ.one => some ⟨E, ⟨Turing.Dir.left, Γ.zero⟩⟩
| F, Γ.zero => some ⟨F, ⟨Turing.Dir.right, Γ.zero⟩⟩
| F, Γ.one => some ⟨K, ⟨Turing.Dir.right, Γ.zero⟩⟩
| G, Γ.zero => some ⟨F, ⟨Turing.Dir.right, Γ.zero⟩⟩
| G, Γ.one => some ⟨H, ⟨Turing.Dir.right, Γ.zero⟩⟩
| H, Γ.zero => some ⟨J, ⟨Turing.Dir.left, Γ.one⟩⟩
| H, Γ.one => some ⟨H, ⟨Turing.Dir.right, Γ.one⟩⟩
| J, Γ.zero => some ⟨G, ⟨Turing.Dir.left, Γ.one⟩⟩
| J, Γ.one => some ⟨J, ⟨Turing.Dir.left, Γ.one⟩⟩
| K, Γ.zero => none
| K, Γ.one => some ⟨B, ⟨Turing.Dir.right, Γ.one⟩⟩


def nth_cfg (init_cfg: Cfg): Nat -> Option Cfg
| 0 => init_cfg
| Nat.succ n => match (nth_cfg init_cfg n) with
                | none => none
                | some cfg =>  step machine cfg


-- https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/binderIdent.20vs.20Ident/near/402516388
def toBinderIdent (i : Ident) : TSyntax ``binderIdent := Unhygienic.run <|
  withRef i `(binderIdent| $i:ident)

elab "forward" g:ident : tactic => withSynthesize <| withMainContext do
  let some ldecl := (← getLCtx).findFromUserName? g.getId
    | throwErrorAt g m!"Identifier {g} not found"
  match ldecl with
  | LocalDecl.cdecl _ _ _ (Expr.app (Expr.app _ (Expr.app (Expr.app _ cfg) i)) _) _ _ =>
      let argType ← inferType i
      if ← isDefEq argType (mkConst ``Nat) then
        let i ← Elab.Term.exprToSyntax i
        let cfg ← Elab.Term.exprToSyntax cfg
        evalTactic (← `(tactic| (
            have h : nth_cfg $cfg ($i + 1) = nth_cfg $cfg ($i + 1) := rfl
            nth_rewrite 2 [nth_cfg] at h
            simp [*, step, Option.map, machine, Turing.Tape.write, Turing.Tape.move] at h
            try simp! [*, -nth_cfg] at h
            try ring_nf at h
            clear $g
            rename_i $(toBinderIdent g)
        )))
      else
        throwError "The second argument of {g} is not a Nat"
  | _ => logInfo m!"please forward on nth_cfg cfg i =  ⟨...⟩"


end Halt
