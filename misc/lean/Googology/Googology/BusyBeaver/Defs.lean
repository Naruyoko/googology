import Mathlib.Computability.TuringMachine

/-!
Modified from turing.TM0 to perform write, move, and state transition in a step, which is standard for BB.
-/


namespace BB

section

open Turing

variable (Γ Λ : Type _) [Inhabited Γ] [Inhabited Λ]

abbrev Stmt : Type _ :=
  Γ × Dir × Option Λ

instance : Inhabited (Stmt Γ Λ) := by infer_instance

abbrev Machine :=
  Λ → Γ → Stmt Γ Λ

instance : Inhabited (Machine Γ Λ) := by infer_instance

/--
The state `none` represents the "halted" state, with output held. This is required because a write, move, and state change are all done in one step.
-/
structure Cfg where
  q : Option Λ
  Tape : Tape Γ
  deriving Inhabited

variable {Γ Λ} (M : Machine Γ Λ) (c : Cfg Γ Λ)

def Halted : Prop :=
  c.q.isNone

def step : Cfg Γ Λ → Option (Cfg Γ Λ) := fun ⟨q, T⟩ =>
  q.map fun q =>
    match M q T.head with
    | ⟨a, d, q'⟩ => ⟨q', (T.write a).move d⟩

def step' (c' : Option (Cfg Γ Λ)) : Option (Cfg Γ Λ) :=
  c' >>= step M

def multistep' (n : ℕ) (c' : Option (Cfg Γ Λ)) : Option (Cfg Γ Λ) :=
  (step' M)^[n] c'

def multistep (n : ℕ) (c : Cfg Γ Λ) : Option (Cfg Γ Λ) :=
  multistep' M n (some c)

def CorrectStep (c₀ c₁ : Cfg Γ Λ) :=
  c₁ ∈ step M c₀

/--
Because we want to be able to talk about precise number of steps until halting we define a relation that takes a set number of steps. -/
def CorrectMultistep (n : ℕ) (c₀ c₁ : Cfg Γ Λ) :=
  c₁ ∈ multistep M n c₀

/-- The statement `reaches M c₀ c₁` means that `c₁` is obtained
  starting from `c₀` after a finite number of steps. -/
def Reaches (c₀ c₁ : Option (Cfg Γ Λ)) : Prop :=
  Relation.ReflTransGen (fun a b => b = step' M a) c₀ c₁

/-- The initial configuration. -/
def init (l : List Γ) : Cfg Γ Λ :=
  ⟨some default, Tape.mk₁ l⟩
#exit
/-- Evaluate a Turing machine on initial input to a final state,
  if it terminates. -/
def eval (M : Machine Γ Λ) (l : List Γ) : Part (ListBlank Γ) :=
  (eval M (init l)).map fun c => c.Tape.right₀

def Supports (S : Set Λ) :=
  default ∈ S ∧ ∀ {q a a' s q'₀ q'}, (a', s, q'₀) = M q a → q ∈ S → q' ∈ q'₀ → q' ∈ S

theorem step_supports (M : Machine Γ Λ) {S} (ss : supports M S) :
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

theorem univ_supports (M : Machine Γ Λ) : supports M Set.univ :=
  ⟨trivial, fun q a a' s q'₀ q' h₁ hq h₂ => trivial⟩

end

notation x "[" M "]▸" y:50 => CorrectStep M x y

notation x "[" M "]▸^[" n "]" y:50 => CorrectMultistep M n x y

end BB
