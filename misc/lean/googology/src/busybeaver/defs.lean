import computability.turing_machine

/-!
Modified from turing.TM0 to perform write, move, and state transition in a step, which is standard for BB. 
-/

namespace BB
section
open turing
parameters (Γ Λ : Type*) [inhabited Γ] [inhabited Λ]

def stmt : Type* :=
Γ × dir × option Λ

instance stmt.inhabited : inhabited stmt :=
by unfold stmt; apply_instance

def machine :=
Λ → Γ → stmt

instance machine.inhabited : inhabited machine :=
by unfold machine; apply_instance

/--
The state `none` represents the "halted" state, with output held. This is required because a write, move, and state change are all done in one step.
-/
structure cfg :=
(q : option Λ)
(tape : tape Γ)

instance cfg.inhabited : inhabited cfg :=
⟨⟨default, default⟩⟩

parameters {Γ Λ}

def halted (c : cfg) : Prop :=
c.q.is_none

def step (M : machine) : cfg → option cfg :=
λ ⟨q, T⟩, q.map $ λ q, match (M q T.head) with ⟨a, d, q'⟩ := ⟨q', (T.write a).move d⟩ end

def step' (M : machine) (c : option cfg) : option cfg :=
c >>= step M

def multistep' (M : machine) (n : ℕ) (c : option cfg) : option cfg :=
step' M^[n] c

def multistep (M : machine) (n : ℕ) (c : cfg) : option cfg :=
multistep' M n (some c)

def correct_step (M : machine) (c₀ c₁ : cfg) :=
c₁ ∈ step M c₀

/-- Because we want to be able to talk about precise number of steps until halting we define a relation that takes a set number of steps. -/
def correct_multistep (M : machine) (n : ℕ) (c₀ c₁ : cfg) :=
c₁ ∈ multistep M n c₀

/-- The statement `reaches M s₁ s₂` means that `s₂` is obtained
  starting from `s₁` after a finite number of steps from `s₂`. -/
def reaches (M : machine) : option cfg → option cfg → Prop :=
λ c₀ c₁, relation.refl_trans_gen (λ a b, b = step' M a) c₀ c₁

/-- The initial configuration. -/
def init (l : list Γ) : cfg :=
⟨default, tape.mk₁ l⟩

/-- Evaluate a Turing machine on initial input to a final state,
  if it terminates. -/
def eval (M : machine) (l : list Γ) : part (list_blank Γ) :=
(eval (step M) (init l)).map (λ c, c.tape.right₀)

def supports (M : machine) (S : set Λ) :=
default ∈ S ∧ ∀ {q a a' s q'₀ q'}, (a', s, q'₀) = M q a → q ∈ S → q' ∈ q'₀ → q' ∈ S

theorem step_supports (M : machine) {S}
  (ss : supports M S) : ∀ {c c' : cfg} {q q'},
  c' ∈ step M c → q ∈ c.q → q ∈ S → q' ∈ c'.q → q' ∈ S :=
begin
  intros c c' q q' h₁ hq h₂ hq',
  cases c with q₀ T,
  cases c' with q'₀ T',
  dsimp at hq hq' h₁,
  subst hq,
  subst hq',
  rcases option.map_eq_some'.mp h₁ with ⟨a, ha, h⟩,
  have := option.some.inj ha,
  subst this,
  rcases hM : M q T.head with ⟨a, d, q'₀⟩,
  refine ss.right hM.symm h₂ _,
  simp [hM, step] at h,
  exact h.left,
end

theorem univ_supports (M : machine) : supports M set.univ :=
⟨trivial, λ q a a' s q'₀ q' h₁ hq h₂, trivial⟩

end

notation x `[` M `]▸` y : 50 := correct_step M x y
notation x `[` M `]▸^[` n `]` y : 50 := correct_multistep M n x y
end BB