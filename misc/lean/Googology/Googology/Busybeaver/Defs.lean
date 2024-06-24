import Mathlib.Computability.TuringMachine

#align_import busybeaver.defs

/-!
Modified from turing.TM0 to perform write, move, and state transition in a step, which is standard for BB.
-/


namespace BB

section

open Turing

parameter (Γ Λ : Type _) [Inhabited Γ] [Inhabited Λ]

def Stmt : Type _ :=
  Γ × Dir × Option Λ

instance Stmt.inhabited : Inhabited stmt := by unfold stmt <;> infer_instance

def Machine :=
  Λ → Γ → stmt

instance Machine.inhabited : Inhabited machine := by unfold machine <;> infer_instance

/--
The state `none` represents the "halted" state, with output held. This is required because a write, move, and state change are all done in one step.
-/
structure Cfg where
  q : Option Λ
  Tape : Tape Γ

instance Cfg.inhabited : Inhabited cfg :=
  ⟨⟨default, default⟩⟩

parameter {Γ Λ}

def Halted (c : cfg) : Prop :=
  c.q.isNone

def step (M : machine) : cfg → Option cfg := fun ⟨q, T⟩ =>
  q.map fun q =>
    match M q T.headI with
    | ⟨a, d, q'⟩ => ⟨q', (T.write a).move d⟩

def step' (M : machine) (c : Option cfg) : Option cfg :=
  c >>= step M

def multistep' (M : machine) (n : ℕ) (c : Option cfg) : Option cfg :=
  (step' M^[n]) c

def multistep (M : machine) (n : ℕ) (c : cfg) : Option cfg :=
  multistep' M n (some c)

def CorrectStep (M : machine) (c₀ c₁ : cfg) :=
  c₁ ∈ step M c₀

/--
Because we want to be able to talk about precise number of steps until halting we define a relation that takes a set number of steps. -/
def CorrectMultistep (M : machine) (n : ℕ) (c₀ c₁ : cfg) :=
  c₁ ∈ multistep M n c₀

/-- The statement `reaches M s₁ s₂` means that `s₂` is obtained
  starting from `s₁` after a finite number of steps from `s₂`. -/
def Reaches (M : machine) : Option cfg → Option cfg → Prop := fun c₀ c₁ =>
  Relation.ReflTransGen (fun a b => b = step' M a) c₀ c₁

/-- The initial configuration. -/
def init (l : List Γ) : cfg :=
  ⟨some default, Tape.mk₁ l⟩

/-- Evaluate a Turing machine on initial input to a final state,
  if it terminates. -/
def eval (M : machine) (l : List Γ) : Part (ListBlank Γ) :=
  (eval (step M) (init l)).map fun c => c.Tape.right₀

def Supports (M : machine) (S : Set Λ) :=
  default ∈ S ∧ ∀ {q a a' s q'₀ q'}, (a', s, q'₀) = M q a → q ∈ S → q' ∈ q'₀ → q' ∈ S

theorem step_supports (M : machine) {S} (ss : supports M S) :
    ∀ {c c' : cfg} {q q'}, c' ∈ step M c → q ∈ c.q → q ∈ S → q' ∈ c'.q → q' ∈ S :=
  by
  intro c c' q q' h₁ hq h₂ hq'
  cases' c with q₀ T
  cases' c' with q'₀ T'
  dsimp at hq hq' h₁
  subst hq
  subst hq'
  rcases option.map_eq_some'.mp h₁ with ⟨a, ha, h⟩
  have := Option.some.inj ha
  subst this
  rcases hM : M q T.head with ⟨a, d, q'₀⟩
  refine' ss.right hM.symm h₂ _
  simp [hM, step] at h
  exact h.left

theorem univ_supports (M : machine) : supports M Set.univ :=
  ⟨trivial, fun q a a' s q'₀ q' h₁ hq h₂ => trivial⟩

end

notation x "[" M "]▸" y:50 => CorrectStep M x y

notation x "[" M "]▸^[" n "]" y:50 => CorrectMultistep M n x y

end BB

