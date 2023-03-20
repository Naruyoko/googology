import data.part
import data.pfun

/- Lots of plagiarism from computability.turing_machine -/

/--
Structure holding the empression part and the accumulator part.
-/
structure accumulator_expression (α : Type*) :=
(expression : α)
(accumulator : ℕ)

/--
Extension of `accumulator_expression` which represents "terminated" state by holding `none` as `expression` and the final output number in `accumulator`.
-/
def accumulator_expression₀ (α : Type*) := accumulator_expression (option α)

structure accumulator_prenotation (α : Type*) :=
(step : accumulator_expression α → accumulator_expression₀ α)

structure accumulator_notation (α : Type*) extends accumulator_prenotation α :=
(limit_expression : α)

namespace accumulator_expression₀
variable {α : Type*}

def is_terminal (p : accumulator_expression₀ α) : bool :=
option.is_none p.expression

def wrap : accumulator_expression α → accumulator_expression₀ α :=
λ ⟨T, n⟩, ⟨some T, n⟩

@[simp] lemma nonterminal_wrap {p : accumulator_expression α} : ¬(wrap p).is_terminal :=
by cases p; exact dec_trivial

def unwrap_nonterminal : Π {p : accumulator_expression₀ α}, ¬p.is_terminal → accumulator_expression α
| ⟨none  , n⟩ h := false.rec _ (h dec_trivial)
| ⟨some T, n⟩ _ := ⟨T, n⟩

@[simp] lemma unwrap_wrap (p : accumulator_expression α) (h : ¬(wrap p).is_terminal): unwrap_nonterminal h = p :=
by cases p; refl

end accumulator_expression₀

namespace accumulator_notation
variable {α : Type*}

section
variable (S : accumulator_notation α)

def init_limit : ℕ → accumulator_expression α :=
λ n, ⟨S.limit_expression, n⟩

def eval₀ : accumulator_expression₀ α → part ℕ :=
pfun.fix (λ p, part.some $ dite p.is_terminal (λ _, sum.inl p.accumulator) (λ h, sum.inr (S.step (accumulator_expression₀.unwrap_nonterminal h))))

/--
Repeatedly applies `S.step` until termination, returning the accumulator then.
-/
def eval : accumulator_expression α → part ℕ :=
eval₀ S ∘ accumulator_expression₀.wrap

def limit : ℕ → part ℕ :=
eval S ∘ init_limit S

lemma eval₀_terminal {p : accumulator_expression₀ α} : p.is_terminal → p.accumulator ∈ eval₀ S p :=
begin
  intro h,
  apply pfun.fix_stop,
  simp *,
end

lemma eval₀_fwd_eq {p : accumulator_expression₀ α} {h : ¬p.is_terminal} : eval₀ S p = eval₀ S (S.step (accumulator_expression₀.unwrap_nonterminal h)) :=
begin
  apply pfun.fix_fwd_eq,
  rw part.mem_some_iff,
  split_ifs,
  refl,
end

lemma eval_eq_eval₀ {p : accumulator_expression α} : eval S p = eval₀ S (accumulator_expression₀.wrap p) := rfl

end

-- def reaches {σ} (f : σ → option σ) : σ → σ → Prop :=
-- refl_trans_gen (λ a b, b ∈ f a)

section
variables (accumulator_step : ℕ → ℕ) (final_step : ℕ → ℕ)

def select_post_step_by_terminating : option α → ℕ → ℕ :=
λ T' n, if option.is_some T' then accumulator_step n else final_step n

@[simp] lemma select_post_step_by_terminating_some (T' : α) (n : ℕ) : select_post_step_by_terminating accumulator_step final_step (some T') n = accumulator_step n := rfl

@[simp] lemma select_post_step_by_terminating_none (n : ℕ) : @select_post_step_by_terminating α accumulator_step final_step none n = final_step n := rfl

def wrap_select_post_step_by_terminating : option α → ℕ → accumulator_expression₀ α :=
λ T' n, ⟨T', select_post_step_by_terminating accumulator_step final_step T' n⟩

@[simp] lemma wrap_select_post_step_by_terminating_some (T' : α) (n : ℕ) : wrap_select_post_step_by_terminating accumulator_step final_step (some T') n = ⟨T', accumulator_step n⟩ := rfl

@[simp] lemma wrap_select_post_step_by_terminating_none (n : ℕ) : @wrap_select_post_step_by_terminating α accumulator_step final_step none n = ⟨none, final_step n⟩ := rfl

end

section
variables (expand : α → ℕ → option α) (expand_transform : ℕ → ℕ) (accumulator_step : ℕ → ℕ) (final_step : ℕ → ℕ)

def expand_select_post_step_by_terminating : α → ℕ → accumulator_expression₀ α :=
λ T n, wrap_select_post_step_by_terminating accumulator_step final_step (expand T $ expand_transform n) n

@[simp] lemma expand_select_post_step_by_terminating_of_is_some_expand {T : α} {n} (h : option.is_some (expand T $ expand_transform n)) : expand_select_post_step_by_terminating expand expand_transform accumulator_step final_step T n = ⟨expand T $ expand_transform n, accumulator_step n⟩ :=
begin
  obtain ⟨_, hT'⟩ := option.is_some_iff_exists.mp h,
  simp_rw [expand_select_post_step_by_terminating, hT'],
  refl,
end

@[simp] lemma expand_select_post_step_by_terminating_of_is_none_expand {T : α} {n} (h : option.is_none (expand T $ expand_transform n)) : expand_select_post_step_by_terminating expand expand_transform accumulator_step final_step T n = ⟨none, final_step n⟩ :=
begin
  simp_rw [expand_select_post_step_by_terminating, option.is_none_iff_eq_none.mp h],
  refl,
end

end

section
variables (expand : α → ℕ → option α) (expand_transform : ℕ → ℕ) (accumulator_step : ℕ → ℕ) (final_step : ℕ → ℕ) {limit_expression : α} (decidable_eq_limit : ∀ T, decidable (T = limit_expression)) (limit_transform : ℕ → ℕ) (limit_step : ℕ → ℕ)

/--
Create an `accumulator_notation` admitting the following function \[\]:

1. T\[n\] = `final_step`(n) (if terminates)
2. `limit_expression`\[n\] = `expand`(T,`limit_transform`(n))\[`limit_step`(n)\]
3. T\[n\] = `expand`(T,`expand_transform`(n))\[`accumulator_step`(n)\] (otherwise)
-/
def mk_prepostapply_step_special_final_limit : accumulator_notation α :=
{ step := λ ⟨T, n⟩, let _ := decidable_eq_limit T in
    if T = limit_expression
    then expand_select_post_step_by_terminating expand limit_transform limit_step final_step T n
    else expand_select_post_step_by_terminating expand expand_transform accumulator_step final_step T n,
  limit_expression := limit_expression }

-- @[simp] lemma mk_prepostapply_step_special_final_limit_none (n : ℕ) : (mk_prepostapply_step_special_final_limit expand expand_transform accumulator_step final_step decidable_eq_limit limit_transform limit_step).step ⟨none,  = {!!} := rfl

/--
Create an `accumulator_notation` admitting the following function \[\]:

1. T\[n\] = n (if terminates)
2. `limit_expression`\[n\] = `expand`(T,`limit_transform`(n))\[`limit_step`(n)\]
3. T\[n\] = `expand`(T,`expand_transform`(n))\[`accumulator_step`(n)\] (otherwise)
-/
def mk_prepostapply_step_special_limit : accumulator_notation α :=
mk_prepostapply_step_special_final_limit expand expand_transform accumulator_step id decidable_eq_limit limit_transform limit_step

/--
Create an `accumulator_notation` admitting the following function \[\]:

1. T\[n\] = n (if terminates)
2. `limit_expression`\[n\] = `expand`(T,n)\[n\]
3. T\[n\] = `expand`(T,`expand_transform`(n))\[`accumulator_step`(n)\] (otherwise)
-/
def mk_prepostapply_step : accumulator_notation α :=
mk_prepostapply_step_special_limit expand expand_transform accumulator_step decidable_eq_limit id id

/--
Create an `accumulator_notation` admitting the following function \[\]:

1. T\[n\] = n (if terminates)
2. `limit_expression`\[n\] = `expand`(T,n)\[n\]
3. T\[n\] = `expand`(T,`accumulator_step`(n))\[`accumulator_step`(n)\] (otherwise)
-/
def mk_preapply_step : accumulator_notation α :=
mk_prepostapply_step expand accumulator_step accumulator_step decidable_eq_limit

/--
Create an `accumulator_notation` admitting the following function \[\]:

1. T\[n\] = n (if terminates)
2. `limit_expression`\[n\] = `expand`(T,n)\[n\]
3. T\[n\] = `expand`(T,n)\[`accumulator_step`(n)\] (otherwise)
-/
def mk_postapply_step : accumulator_notation α :=
mk_prepostapply_step expand id accumulator_step decidable_eq_limit

/--
Create an `accumulator_notation` admitting the following function \[\]:

1. T\[n\] = n (if terminates)
2. `limit_expression`\[n\] = `expand`(T,n)\[n\]
3. T\[n\] = `expand`(T,n)\[`accumulator_step`(n)\] (otherwise)
-/
def mk_id_step : accumulator_notation α :=
mk_prepostapply_step expand id id decidable_eq_limit
end

section 
variables (expand : α → ℕ → option α) (expand_transform : ℕ → ℕ) (accumulator_step : ℕ → ℕ) (limit_seq : ℕ → α)
/--
Extend `expand` at singular point using `limit_seq`
-/
def limit_point_extend : option α → ℕ → option (option α)
| none     n := some (some (limit_seq n))
| (some T) n := some <$> expand T n

@[simp] lemma limit_point_extend_some (T : α) (n : ℕ) : limit_point_extend expand limit_seq (some T) n = some <$> expand T n := rfl

@[simp] lemma limit_point_extend_some_of_is_some_extend {T : α} {n : ℕ} (h : option.is_some (expand T n)) : limit_point_extend expand limit_seq (some T) n = some (expand T n) :=
begin
  obtain ⟨_, hT'⟩ := option.is_some_iff_exists.mp h,
  simp [hT'],
end

@[simp] lemma limit_point_extend_some_of_is_none_extend {T : α} {n : ℕ} (h : option.is_none (expand T n)) : limit_point_extend expand limit_seq (some T) n = none :=
by simp [option.is_none_iff_eq_none.mp h]

@[simp] lemma limit_point_extend_none (n : ℕ) : limit_point_extend expand limit_seq none n = some (some (limit_seq n)) := rfl

lemma is_some_limit_point_extend_some_iff (T : α) (n : ℕ) : option.is_some (limit_point_extend expand limit_seq (some T) n) ↔ option.is_some (expand T n) :=
begin
  split; intro h,
  { contrapose h,
    simp [option.is_none_iff_eq_none] at *,
    assumption },
  { simp * }
end

lemma is_none_limit_point_extend_some_iff (T : α) (n : ℕ) : option.is_none (limit_point_extend expand limit_seq (some T) n) ↔ option.is_none (expand T n) :=
begin
  have : ∀ {α} {x : option α}, option.is_none x ↔ ¬option.is_some x,
  by intros _ x; cases x; tauto,
  iterate 2 { rw this },
  rw not_iff_not,
  exact is_some_limit_point_extend_some_iff _ _ _ _,
end

lemma is_some_limit_point_extend_none (n : ℕ) : option.is_some (limit_point_extend expand limit_seq none n) :=
by tauto

lemma is_some_limit_point_iff (T : option α) (n : ℕ) : option.is_some (limit_point_extend expand limit_seq T n) ↔ (∃ x : α, T = some x ∧ option.is_some (expand x n)) ∨ option.is_none T :=
begin
  cases T,
  { tauto },
  { simp [-accumulator_notation.limit_point_extend_some],
    exact is_some_limit_point_extend_some_iff _ _ _ _ }
end

lemma is_none_limit_point_iff (T : option α) (n : ℕ) : option.is_none (limit_point_extend expand limit_seq T n) ↔ (∃ x : α, T = some x ∧ option.is_none (expand x n)) :=
begin
  cases T,
  { tauto },
  { simp [-accumulator_notation.limit_point_extend_some],
    exact is_none_limit_point_extend_some_iff _ _ _ _ }
end

lemma get_of_is_some_limit_point_extend {T : option α} {n : ℕ} (h : option.is_some (limit_point_extend expand limit_seq T n)) : option.get h = option.elim (limit_seq n) (λ x, expand x n) T :=
begin
  have hT := (is_some_limit_point_iff _ _ _ _).mp h,
  cases hT,
  { cases hT, simp * },
  { have := option.eq_none_of_is_none hT,
    subst this,
    tauto }
end

lemma is_some_get_of_is_some_limit_point_extend {T : option α} {n : ℕ} (h : option.is_some (limit_point_extend expand limit_seq T n)) : option.is_some (option.get h) :=
begin
  have hT := (is_some_limit_point_iff _ _ _ _).mp h,
  cases hT,
  { cases hT with x hx,
    simp * },
  { have := option.eq_none_of_is_none hT,
    subst this,
    tauto }
end

/--
Create an `accumulator_notation` admitting the following function \[\] and limit function Lim:

1. T\[n\] = n (if terminates)
2. T\[n\] = `expand`(T,`expand_transform`(n))\[`accumulator_step`(n)\] (otherwise)
3. Lim(n) = `limit_seq`(n)\[n\]
-/
def mk_limit_seq : accumulator_notation (option α) :=
mk_prepostapply_step (limit_point_extend expand limit_seq) expand_transform accumulator_step (λ _, option.decidable_eq_none)

end

/--
Emulate Hardy hierarchy on top of set of terms `α`, "fundamental sequence" `fund`, and `decidable` `is_succ`:

1. H_T(n) = n (if terminates)
2. H_T(n) = H_{`expand`(T,n)}(n+1) (if `is_succ`(T))
3. H_T(n) = H_{`expand`(T,n)}(n) (otherwise)
-/
def simulate_Hardy (fund : α → ℕ → option α) {is_succ : α → Prop} (decidable_is_succ : decidable_pred is_succ) : accumulator_prenotation α :=
{ step := λ ⟨T, n⟩, ⟨fund T n, if is_succ T then n+1 else n⟩ }

-- /--
-- Emulate fast growing hierarchy on top of set of terms `α`, "fundamental sequence" `fund`, and `decidable` `is_succ`:

-- 1. f_T(n) = n+1 (if terminates)
-- 2. f_T(n) = H_{`expand`(T,n)}(n+1) (if `is_succ`(T))
-- 3. f_T(n) = H_{`expand`(T,n)}(n) (otherwise)
-- -/
-- def simulate_FGH (fund : α → ℕ → option α) {is_succ : α → Prop} (decidable_is_succ : decidable_pred is_succ) : accumulator_prenotation α :=
-- { step := λ ⟨T, n⟩, (fund T n).map (λ T', ⟨T', if is_succ T then n+1 else n⟩) }

end accumulator_notation