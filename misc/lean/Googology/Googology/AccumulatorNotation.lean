import Mathlib.Data.List.Basic
import Mathlib.Data.Part
import Mathlib.Data.Pfun
import Mathlib.Logic.Relation

#align_import accumulator_notation

-- Lots of plagiarism from computability.turing_machine
/-- Structure holding the empression part and the accumulator part. -/
structure AccumulatorExpression (α : Type _) where
  expression : α
  accumulator : ℕ

/--
Extension of `accumulator_expression` which represents "terminated" state by holding `none` as `expression` and the final output number in `accumulator`.
-/
def AccumulatorExpression₀ (α : Type _) :=
  AccumulatorExpression (Option α)

structure AccumulatorPrenotation (α : Type _) where
  step : AccumulatorExpression α → AccumulatorExpression₀ α

structure AccumulatorNotation (α : Type _) extends AccumulatorPrenotation α where
  limitExpression : α

namespace AccumulatorExpression₀

variable {α : Type _}

def isTerminal (p : AccumulatorExpression₀ α) : Bool :=
  Option.isNone p.expression

def wrap : AccumulatorExpression α → AccumulatorExpression₀ α := fun ⟨T, n⟩ => ⟨some T, n⟩

@[simp]
theorem nonterminal_wrap {p : AccumulatorExpression α} : ¬(wrap p).isTerminal := by
  rw [← Bool.not_iff_not]
  rfl

def unwrapNonterminal : ∀ {p : AccumulatorExpression₀ α}, ¬p.isTerminal → AccumulatorExpression α
  | ⟨none,   _⟩, h => absurd rfl h
  | ⟨some T, n⟩, _ => ⟨T, n⟩

@[simp]
theorem unwrap_wrap (p : AccumulatorExpression α) :
  unwrapNonterminal (nonterminal_wrap (p := p)) = p := rfl

end AccumulatorExpression₀

namespace AccumulatorNotation

variable {α : Type _}

section

variable (S : AccumulatorNotation α)

def initLimit : ℕ → AccumulatorExpression α := fun n => ⟨S.limitExpression, n⟩

def eval₀ : AccumulatorExpression₀ α → Part ℕ :=
  PFun.fix fun p =>
    Part.some <|
      dite p.isTerminal (fun _ => Sum.inl p.accumulator) fun h =>
        Sum.inr (S.step (AccumulatorExpression₀.unwrapNonterminal h))

/-- Repeatedly applies `S.step` until termination, returning the accumulator then.
-/
def eval : AccumulatorExpression α → Part ℕ :=
  eval₀ S ∘ AccumulatorExpression₀.wrap

theorem eval_eq_eval₀ {p : AccumulatorExpression α} :
    eval S p = eval₀ S (AccumulatorExpression₀.wrap p) :=
  rfl

def limit : ℕ → Part ℕ :=
  eval S ∘ initLimit S

theorem eval₀_terminal {p : AccumulatorExpression₀ α} : p.isTerminal → p.accumulator ∈ eval₀ S p :=
  by
  intro h
  apply PFun.fix_stop
  simp [*]

theorem eval₀_step_eq {p : AccumulatorExpression₀ α} (h : ¬p.isTerminal) :
    eval₀ S p = eval₀ S (S.step (AccumulatorExpression₀.unwrapNonterminal h)) :=
  by
  apply PFun.fix_fwd_eq
  rw [Part.mem_some_iff]
  split_ifs
  rfl

theorem dom_eval₀_terminal {p : AccumulatorExpression₀ α} : p.isTerminal → (eval₀ S p).Dom :=
  fun h => Part.dom_iff_mem.mpr ⟨_, eval₀_terminal S h⟩

theorem dom_eval₀_step {p : AccumulatorExpression₀ α} (h : ¬p.isTerminal) :
    (eval₀ S p).Dom = (eval₀ S (S.step (AccumulatorExpression₀.unwrapNonterminal h))).Dom := by
  rw [eval₀_step_eq]

def eval₀IsTotalAt (T : Option α) : Prop :=
  ∀ n, (eval₀ S ⟨T, n⟩).Dom

def evalIsTotalAt (T : α) : Prop :=
  ∀ n, (eval S ⟨T, n⟩).Dom

theorem dom_of_all_dom_eval₀_step {T : α} :
    (∀ n, S.eval₀IsTotalAt (S.step ⟨T, n⟩).expression) → S.evalIsTotalAt T := by
  intro h n
  rw [eval_eq_eval₀]
  rw [eval₀_step_eq S AccumulatorExpression₀.nonterminal_wrap]
  apply h

end

section

variable {β : Type _} (f : α → β → Option α)

/--
`reachable f a b` denotes the reachability of `a` to `b` by recursively iterating into the first argument of `f` and arbitrary second arguments.
-/
def Reachable : Option α → Option α → Prop :=
  Relation.ReflTransGen (Option.elim' (fun _ => False) fun a b => ∃ c, b = f a c)

theorem reflexive_reachable : Reflexive (Reachable f) := fun _ => Relation.ReflTransGen.refl

theorem transitive_reachable : Transitive (Reachable f) := fun _ _ _ => Relation.ReflTransGen.trans

theorem reachable_iff_exists_list_args {a b : Option α} :
    Reachable f a b ↔
      ∃ l : List β,
        (List.scanl (fun (c : Option α) d => c >>= fun c' => f c' d) a l).dropLast.all
            Option.isSome ∧
          List.foldl (fun (c : Option α) d => c >>= fun c' => f c' d) a l = b := by
  have scanl_ne_nil : ∀ a l, List.scanl (fun (c : Option α) d => c >>= fun c' => f c' d) a l ≠ [] :=
    by introv ; cases l <;> tauto
  simp only [Option.bind_eq_bind] at scanl_ne_nil ⊢
  constructor
  · intro hab
    unfold Reachable at hab
    refine Relation.ReflTransGen.head_induction_on hab ?_ ?_
    · use List.nil
      tauto
    · clear! a
      intro a c hac hcb IH
      have ha_some : a.isSome := by cases a <;> tauto
      obtain ⟨a, rfl⟩ := Option.isSome_iff_exists.mp ha_some
      rcases hac with ⟨d, rfl⟩
      cases' IH with l hl
      use d :: l
      simp only [List.scanl, Option.some_bind]
      rw [List.dropLast_cons_of_ne_nil (scanl_ne_nil _ _)]
      tauto
  · intro hab
    rcases hab with ⟨l, ⟨hsome, hl⟩⟩
    unfold Reachable
    induction' l with d l IH generalizing a
    · simp_all
      trivial
    · simp only [List.scanl] at hsome
      rw [List.dropLast_cons_of_ne_nil (scanl_ne_nil _ _)] at hsome
      have ha_some : a.isSome := by
        rw [← Option.ne_none_iff_isSome]
        intro H
        subst H
        contradiction
      obtain ⟨a, rfl⟩ := Option.isSome_iff_exists.mp ha_some
      rw [Relation.ReflTransGen.cases_head_iff]
      right
      use f a d
      constructor
      · use d
      · rw [List.foldl_cons, Option.some_bind] at hl
        rw [List.all_cons, Bool.and_eq_true, Option.some_bind] at hsome
        exact IH hsome.right hl

end

section

variable (accumulator_step : ℕ → ℕ) (final_step : ℕ → ℕ)

def selectPostStepByTerminating : Option α → ℕ → ℕ := fun T' n =>
  if Option.isSome T' then accumulator_step n else final_step n

@[simp]
theorem selectPostStepByTerminating_some (T' : α) (n : ℕ) :
    selectPostStepByTerminating accumulator_step final_step (some T') n = accumulator_step n :=
  rfl

@[simp]
theorem selectPostStepByTerminating_none (n : ℕ) :
    @selectPostStepByTerminating α accumulator_step final_step none n = final_step n :=
  rfl

def wrapSelectPostStepByTerminating : Option α → ℕ → AccumulatorExpression₀ α := fun T' n =>
  ⟨T', selectPostStepByTerminating accumulator_step final_step T' n⟩

@[simp]
theorem wrapSelectPostStepByTerminating_some (T' : α) (n : ℕ) :
    wrapSelectPostStepByTerminating accumulator_step final_step (some T') n =
      ⟨T', accumulator_step n⟩ :=
  rfl

@[simp]
theorem wrapSelectPostStepByTerminating_none (n : ℕ) :
    @wrapSelectPostStepByTerminating α accumulator_step final_step none n = ⟨none, final_step n⟩ :=
  rfl

end

section

variable (expand : α → ℕ → Option α) (expand_transform : ℕ → ℕ) (accumulator_step : ℕ → ℕ)
  (final_step : ℕ → ℕ)

def expandSelectPostStepByTerminating : α → ℕ → AccumulatorExpression₀ α := fun T n =>
  wrapSelectPostStepByTerminating accumulator_step final_step (expand T <| expand_transform n) n

@[simp]
theorem expandSelectPostStepByTerminating_of_isSome_expand {T : α} {n}
    (h : Option.isSome (expand T <| expand_transform n)) :
    expandSelectPostStepByTerminating expand expand_transform accumulator_step final_step T n =
      ⟨expand T <| expand_transform n, accumulator_step n⟩ :=
  by
  obtain ⟨_, hT'⟩ := Option.isSome_iff_exists.mp h
  simp_rw [expandSelectPostStepByTerminating, hT']
  rfl

@[simp]
theorem expandSelectPostStepByTerminating_of_isNone_expand {T : α} {n}
    (h : Option.isNone (expand T <| expand_transform n)) :
    expandSelectPostStepByTerminating expand expand_transform accumulator_step final_step T n =
      ⟨none, final_step n⟩ :=
  by
  simp_rw [expandSelectPostStepByTerminating, Option.isNone_iff_eq_none.mp h]
  rfl

end

section

variable (expand : α → ℕ → Option α) (expand_transform : ℕ → ℕ) (accumulator_step : ℕ → ℕ)
  (final_step : ℕ → ℕ) {limitExpression : α}
  (decidable_eq_limit : ∀ T, Decidable (T = limitExpression)) (limit_transform : ℕ → ℕ)
  (limit_step : ℕ → ℕ)

/-- Create an `accumulator_notation` admitting the following function \[\]:

1. T\[n\] = `final_step`(n) (if terminates)
2. `limitExpression`\[n\] = `expand`(T,`limit_transform`(n))\[`limit_step`(n)\]
3. T\[n\] = `expand`(T,`expand_transform`(n))\[`accumulator_step`(n)\] (otherwise)
-/
def mkPrepostapplyStepSpecialFinalLimit : AccumulatorNotation α :=
  { step := fun ⟨T, n⟩ =>
      let _ := decidable_eq_limit T
      if T = limitExpression then
        expandSelectPostStepByTerminating expand limit_transform limit_step final_step T n
      else expandSelectPostStepByTerminating expand expand_transform accumulator_step final_step T n
    limitExpression }

-- @[simp] lemma mk_prepostapply_step_special_final_limit_none (n : ℕ) : (mk_prepostapply_step_special_final_limit expand expand_transform accumulator_step final_step decidable_eq_limit limit_transform limit_step).step ⟨none,  = {!!} := rfl
/-- Create an `accumulator_notation` admitting the following function \[\]:

1. T\[n\] = n (if terminates)
2. `limitExpression`\[n\] = `expand`(T,`limit_transform`(n))\[`limit_step`(n)\]
3. T\[n\] = `expand`(T,`expand_transform`(n))\[`accumulator_step`(n)\] (otherwise)
-/
def mkPrepostapplyStepSpecialLimit : AccumulatorNotation α :=
  mkPrepostapplyStepSpecialFinalLimit expand expand_transform accumulator_step id decidable_eq_limit
    limit_transform limit_step

/-- Create an `accumulator_notation` admitting the following function \[\]:

1. T\[n\] = n (if terminates)
2. `limitExpression`\[n\] = `expand`(T,n)\[n\]
3. T\[n\] = `expand`(T,`expand_transform`(n))\[`accumulator_step`(n)\] (otherwise)
-/
def mkPrepostapplyStep : AccumulatorNotation α :=
  mkPrepostapplyStepSpecialLimit expand expand_transform accumulator_step decidable_eq_limit id id

/-- Create an `accumulator_notation` admitting the following function \[\]:

1. T\[n\] = n (if terminates)
2. `limitExpression`\[n\] = `expand`(T,n)\[n\]
3. T\[n\] = `expand`(T,`accumulator_step`(n))\[`accumulator_step`(n)\] (otherwise)
-/
def mkPreapplyStep : AccumulatorNotation α :=
  mkPrepostapplyStep expand accumulator_step accumulator_step decidable_eq_limit

/-- Create an `accumulator_notation` admitting the following function \[\]:

1. T\[n\] = n (if terminates)
2. `limitExpression`\[n\] = `expand`(T,n)\[n\]
3. T\[n\] = `expand`(T,n)\[`accumulator_step`(n)\] (otherwise)
-/
def mkPostapplyStep : AccumulatorNotation α :=
  mkPrepostapplyStep expand id accumulator_step decidable_eq_limit

/-- Create an `accumulator_notation` admitting the following function \[\]:

1. T\[n\] = n (if terminates)
2. `limitExpression`\[n\] = `expand`(T,n)\[n\]
3. T\[n\] = `expand`(T,n)\[`accumulator_step`(n)\] (otherwise)
-/
def mkIdStep : AccumulatorNotation α :=
  mkPrepostapplyStep expand id id decidable_eq_limit

end

section

variable (expand : α → ℕ → Option α) (expand_transform : ℕ → ℕ) (accumulator_step : ℕ → ℕ)
  (limit_seq : ℕ → α)

/-- Extend `expand` at singular point using `limit_seq`
-/
def limitPointExtend : Option α → ℕ → Option (Option α)
  | none, n => some (some (limit_seq n))
  | some T, n => some <$> expand T n

@[simp]
theorem limitPointExtend_some (T : α) (n : ℕ) :
    limitPointExtend expand limit_seq (some T) n = some <$> expand T n :=
  rfl

@[simp]
theorem limitPointExtend_some_of_isSome_extend {T : α} {n : ℕ} (h : Option.isSome (expand T n)) :
    limitPointExtend expand limit_seq (some T) n = some (expand T n) :=
  by
  obtain ⟨_, hT'⟩ := Option.isSome_iff_exists.mp h
  simp [hT']

@[simp]
theorem limitPointExtend_some_of_isNone_extend {T : α} {n : ℕ} (h : Option.isNone (expand T n)) :
    limitPointExtend expand limit_seq (some T) n = none := by simp [Option.isNone_iff_eq_none.mp h]

@[simp]
theorem limitPointExtend_none (n : ℕ) :
    limitPointExtend expand limit_seq none n = some (some (limit_seq n)) :=
  rfl

theorem isSome_limitPointExtend_some_eq (T : α) (n : ℕ) :
    Option.isSome (limitPointExtend expand limit_seq (some T) n) = Option.isSome (expand T n) :=
  by
  cases h : expand T n <;> simp [h]

theorem isNone_limitPointExtend_some_eq (T : α) (n : ℕ) :
    Option.isNone (limitPointExtend expand limit_seq (some T) n) = Option.isNone (expand T n) :=
  by
  have : ∀ {α} {x : Option α}, Option.isNone x = !Option.isSome x := by
    intro _ x
    cases x <;> tauto
  iterate 2 rw [this]
  rw [isSome_limitPointExtend_some_eq]

theorem isSome_limitPointExtend_none (n : ℕ) :
    Option.isSome (limitPointExtend expand limit_seq none n) := by tauto

theorem isSome_limit_point_iff (T : Option α) (n : ℕ) :
    Option.isSome (limitPointExtend expand limit_seq T n) ↔
      (∃ x : α, T = some x ∧ Option.isSome (expand x n)) ∨ Option.isNone T :=
  by
  cases T <;> simp [↓isSome_limitPointExtend_some_eq]

theorem isNone_limit_point_iff (T : Option α) (n : ℕ) :
    Option.isNone (limitPointExtend expand limit_seq T n) =
      ∃ x : α, T = some x ∧ Option.isNone (expand x n) :=
  by
  cases T <;> simp [↓isNone_limitPointExtend_some_eq]

theorem get_of_isSome_limitPointExtend {T : Option α} {n : ℕ}
    (h : Option.isSome (limitPointExtend expand limit_seq T n)) :
    Option.get _ h = Option.elim' (some (limit_seq n)) (fun x => expand x n) T :=
  by
  have hT := (isSome_limit_point_iff _ _ _ _).mp h
  cases hT with
  | inl hT =>
    rcases hT with ⟨x, hx⟩
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hx.right
    simp [*]
  | inr hT =>
    simp only [Option.eq_none_of_isNone hT]
    tauto

theorem isSome_get_of_isSome_limitPointExtend {T : Option α} {n : ℕ}
    (h : Option.isSome (limitPointExtend expand limit_seq T n)) : Option.isSome (Option.get _ h) :=
  by
  have hT := (isSome_limit_point_iff _ _ _ _).mp h
  cases hT with
  | inl hT =>
    rcases hT with ⟨x, hx⟩
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hx.right
    simp [*]
  | inr hT =>
    simp only [Option.eq_none_of_isNone hT]
    tauto

/-- Create an `accumulator_notation` admitting the following function \[\] and limit function Lim:

1. T\[n\] = n (if terminates)
2. T\[n\] = `expand`(T,`expand_transform`(n))\[`accumulator_step`(n)\] (otherwise)
3. Lim(n) = `limit_seq`(n)\[n\]
-/
def mkLimitSeq : AccumulatorNotation (Option α) :=
  mkPrepostapplyStep (limitPointExtend expand limit_seq) expand_transform accumulator_step fun _ =>
    Option.decidable_eq_none

end

/--
Emulate Hardy hierarchy on top of set of terms `α`, "fundamental sequence" `fund`, and `decidable` `is_succ`:

1. H_T(n) = n (if terminates)
2. H_T(n) = H_{`expand`(T,n)}(n+1) (if `is_succ`(T))
3. H_T(n) = H_{`expand`(T,n)}(n) (otherwise)
-/
def simulateHardy (fund : α → ℕ → Option α) {is_succ : α → Prop} [DecidablePred is_succ] :
    AccumulatorPrenotation α
    where step := fun ⟨T, n⟩ => ⟨fund T n, if is_succ T then n + 1 else n⟩

-- /--
-- Emulate fast growing hierarchy on top of set of terms `α`, "fundamental sequence" `fund`, and `decidable` `is_succ`:
-- 1. f_T(n) = n+1 (if terminates)
-- 2. f_T(n) = H_{`expand`(T,n)}(n+1) (if `is_succ`(T))
-- 3. f_T(n) = H_{`expand`(T,n)}(n) (otherwise)
-- -/
-- def simulate_FGH (fund : α → ℕ → option α) {is_succ : α → Prop} (decidable_is_succ : decidable_pred is_succ) : accumulator_prenotation α :=
-- { step := λ ⟨T, n⟩, (fund T n).map (λ T', ⟨T', if is_succ T then n+1 else n⟩) }

end AccumulatorNotation
