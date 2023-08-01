import
  data.fintype.sigma
  data.pnat.basic
  order.iterate
  order.well_founded

namespace ysequence

section intro
variables {α β γ : Type}

instance (p : Prop) [decidable p] (q : α → Prop) [decidable_pred q] : decidable_pred $ option.elim p q :=
by { intro o, cases o; simp; apply_instance }

instance option.cases_on.decidable (o : option α) (p : Prop) [decidable p]
  (q : α → Prop) [decidable_pred q] : decidable $ option.cases_on o p q :=
by { cases o; simp; apply_instance }

instance option.cases_on.decidable_pred (p : Prop) [decidable p] (q : α → Prop) [decidable_pred q] :
  decidable_pred (λ o, option.cases_on o p q) :=
by { intro o, cases o; simp; apply_instance }

instance (r : α → α → Prop) [decidable_rel r] : decidable_pred $ function.uncurry r :=
by { rw function.uncurry, apply_instance }

def iterate_eventually_none (f : α → option α) : Prop :=
∀ (x : option α), ∃ (k : ℕ), (flip bind f)^[k] x = none

lemma iterate_eventually_none_or_mem_of_iterate_eventually_none {f : α → option α} (hf : iterate_eventually_none f)
  (p : set α) (x : α) : ∃ (k : ℕ), option.elim true p $ (flip bind f)^[k] $ some x :=
begin
  rcases hf (some x) with ⟨k, hk⟩,
  use k,
  rw hk,
  triv
end

def find_index_iterate_of_iterate_eventually_none {f : α → option α} (hf : iterate_eventually_none f)
  {p : set α} (decidable_p : decidable_pred p) : α → ℕ :=
λ x, nat.find (iterate_eventually_none_or_mem_of_iterate_eventually_none hf p x)

lemma find_index_iterate_spec {f : α → option α} (hf : iterate_eventually_none f)
  {p : set α} (decidable_p : decidable_pred p) (x : α) :
  option.elim true p $ (flip bind f)^[find_index_iterate_of_iterate_eventually_none hf decidable_p x] $ some x :=
nat.find_spec (iterate_eventually_none_or_mem_of_iterate_eventually_none hf p x)

lemma find_index_iterate_min {f : α → option α} (hf : iterate_eventually_none f)
  {p : set α} (decidable_p : decidable_pred p) (x : α) {k : ℕ} :
  k < find_index_iterate_of_iterate_eventually_none hf decidable_p x →
  ¬(option.elim true p $ (flip bind f)^[k] $ some x) :=
nat.find_min (iterate_eventually_none_or_mem_of_iterate_eventually_none hf p x)

lemma find_index_iterate_eq_iff {f : α → option α} (hf : iterate_eventually_none f)
  {p : set α} (decidable_p : decidable_pred p) (x : α) (k : ℕ) :
  find_index_iterate_of_iterate_eventually_none hf decidable_p x = k ↔
    (option.elim true p $ (flip bind f)^[k] $ some x) ∧
    ∀ (l < k), ¬(option.elim true p $ (flip bind f)^[l] $ some x) :=
nat.find_eq_iff (iterate_eventually_none_or_mem_of_iterate_eventually_none hf p x)

def find_iterate_of_iterate_eventually_none {f : α → option α} (hf : iterate_eventually_none f)
  {p : set α} (decidable_p : decidable_pred p) : α → option α :=
λ x, (flip bind f)^[find_index_iterate_of_iterate_eventually_none hf decidable_p x] $ some x

lemma find_iterate_spec {f : α → option α} (hf : iterate_eventually_none f)
  {p : set α} (decidable_p : decidable_pred p) (x : α) :
  option.elim true p $ find_iterate_of_iterate_eventually_none hf decidable_p x :=
find_index_iterate_spec _ _ _

lemma find_iterate_is_some_iff {f : α → option α} (hf : iterate_eventually_none f)
  {p : set α} (decidable_p : decidable_pred p) (x : α) :
  (find_iterate_of_iterate_eventually_none hf decidable_p x).is_some ↔
    ∃ {k : ℕ} (h : ((flip bind f)^[k] $ some x).is_some), option.get h ∈ p :=
begin
  split,
  { intro h,
    refine ⟨_, h, _⟩,
    obtain ⟨y, hy⟩ := option.is_some_iff_exists.mp h,
    conv in (option.get _)
    begin
      congr,
      change find_iterate_of_iterate_eventually_none hf decidable_p x,
    end,
    have := find_iterate_spec hf decidable_p x,
    simp_rw hy at ⊢ this,
    exact this },
  { intro h,
    rcases h with ⟨k, hk₁, hk₂⟩,
    by_contra H,
    apply @find_index_iterate_min _ _ hf _ decidable_p x k,
    { clear hk₂,
      contrapose hk₁ with H',
      rw not_lt at H',
      refine nat.le_induction H _ k H',
      intros k _ IH,
      rw option.not_is_some_iff_eq_none at IH ⊢,
      rw [function.iterate_succ_apply', IH],
      refl },
    { obtain ⟨y, hy⟩ := option.is_some_iff_exists.mp hk₁,
      simp_rw hy at hk₂ ⊢,
      exact hk₂ } }
end

lemma find_iterate_eq_none_iff {f : α → option α} (hf : iterate_eventually_none f)
  {p : set α} (decidable_p : decidable_pred p) (x : α) :
  find_iterate_of_iterate_eventually_none hf decidable_p x = none ↔
    ∀ {k : ℕ} (h : ((flip bind f)^[k] $ some x).is_some), option.get h ∉ p :=
begin
  rw ← not_iff_not,
  push_neg,
  rw option.ne_none_iff_is_some,
  exact find_iterate_is_some_iff _ _ _
end

lemma find_index_iterate_pos_of_nin {f : α → option α} (hf : iterate_eventually_none f)
  {p : set α} (decidable_p : decidable_pred p) {x : α} (hn : x ∉ p) :
  0 < find_index_iterate_of_iterate_eventually_none hf decidable_p x :=
begin
  rw pos_iff_ne_zero,
  intro H,
  have := find_index_iterate_spec hf decidable_p x,
  rw H at this,
  contradiction
end

def to_none_or_lt_id (f : ℕ → option ℕ) : Prop :=
∀ (n : ℕ), with_bot.has_lt.lt (f n) n

theorem iterate_eventually_none_of_to_none_or_lt_id {f : ℕ → option ℕ} (hf : to_none_or_lt_id f) :
  iterate_eventually_none f :=
begin
  refine λ n, @is_well_founded.induction (with_bot ℕ) (<) is_well_order.to_is_well_founded _ n _,
  intros n IH,
  cases n with n,
  { exact ⟨0, rfl⟩ },
  { choose! k h using IH,
    exact ⟨k (f n) + 1, h _ (hf n)⟩ }
end

def find_iterate_of_to_none_or_lt_id {f : ℕ → option ℕ} (hf : to_none_or_lt_id f)
  {p : set ℕ} (decidable_p : decidable_pred p) : ℕ → option ℕ :=
find_iterate_of_iterate_eventually_none (iterate_eventually_none_of_to_none_or_lt_id hf) decidable_p

lemma iterate_bind_none (f : α → option α) (n : ℕ) : (flip bind f)^[n] none = none :=
flip n.rec_on (by { intros n IH, simpa only [function.iterate_succ_apply', IH] }) rfl

theorem to_none_or_lt_id_iterate_succ {f : ℕ → option ℕ} (hf : to_none_or_lt_id f) (n k : ℕ) :
  with_bot.has_lt.lt ((flip bind f)^[k + 1] $ some n : option ℕ) n :=
begin
  induction k with k IH,
  { exact hf n },
  { rw function.iterate_succ_apply',
    cases ((flip bind f)^[k + 1] $ some n) with l,
    { exact with_bot.bot_lt_coe n },
    { exact lt_trans (hf l) IH } }
end

theorem to_none_or_lt_id_iterate_pos {f : ℕ → option ℕ} (hf : to_none_or_lt_id f)
  (n : ℕ) {k : ℕ} (hk : 0 < k) : with_bot.has_lt.lt ((flip bind f)^[k] $ some n : option ℕ) n :=
begin
  cases k,
  { exact absurd hk dec_trivial },
  { exact to_none_or_lt_id_iterate_succ hf n k }
end

theorem to_none_or_lt_id_find_iterate_of_nin {f : ℕ → option ℕ} (hf : to_none_or_lt_id f)
  {p : set ℕ} (decidable_p : decidable_pred p) {n : ℕ} (hn : n ∉ p) :
  with_bot.has_lt.lt (find_iterate_of_to_none_or_lt_id hf decidable_p n : option ℕ) n :=
to_none_or_lt_id_iterate_pos hf _ (find_index_iterate_pos_of_nin _ _ hn)

theorem to_none_or_lt_id_find_iterate_of_all_nin {f : ℕ → option ℕ} (hf : to_none_or_lt_id f)
  {g : ℕ → set ℕ} (hg₁ : ∀ n, decidable_pred $ g n) (hg₂ : ∀ n, n ∉ g n) :
  to_none_or_lt_id $ (λ n, find_iterate_of_to_none_or_lt_id hf (hg₁ n) n) :=
λ n, to_none_or_lt_id_find_iterate_of_nin hf (hg₁ n) (hg₂ n)

example :
  let p := λ n, @find_iterate_of_to_none_or_lt_id
    (λ m, nat.cases_on m none some)
    begin
      intro m,
      cases m,
      { exact with_bot.bot_lt_coe 0 },
      { exact with_bot.coe_lt_coe.mpr (nat.lt_succ_self m) }
    end
    ({1, 3, 4, 6} \ {n})
    (by apply_instance)
    n in
  (p <$> [0, 1, 2, 8] = [none, none, some 1, some 6]) ∧
    to_none_or_lt_id p :=
⟨begin
  simp [find_iterate_of_to_none_or_lt_id,
    find_iterate_of_iterate_eventually_none,
    find_index_iterate_of_iterate_eventually_none],
  repeat { split },
  work_on_goal 1 { suffices : nat.find _ = 1, rw this, refl },
  work_on_goal 2 { suffices : nat.find _ = 2, rw this, refl },
  work_on_goal 3 { suffices : nat.find _ = 1, rw this, refl },
  work_on_goal 4 { suffices : nat.find _ = 2, rw this, refl },
  all_goals { rw nat.find_eq_iff, simp [flip], dec_trivial },
end,
begin
  apply to_none_or_lt_id_find_iterate_of_all_nin,
  intro n,
  simp [(∈)],
  exact not_and_not_right.mpr (congr_fun rfl)
end⟩


def index (s : list α) : Type := fin s.length

def index.index {s : list α} (i :index s) : ℕ := i.val

def index.val {s : list α} (i : index s) : α := s.nth_le i.index i.property

lemma index.val_mem {s : list α} (i : index s) : i.val ∈ s := list.nth_le_mem _ _ _

instance (s : list α) : fintype (index s) := fin.fintype _

def in_index_elim {s : list α} (f : index s → β) (g : β) (i : ℕ) : β :=
if h : i < s.length then f ⟨i, h⟩ else g

@[simp] lemma in_index_elim_yes {s : list α} (f : index s → β) (g : β) (i : index s) :
  in_index_elim f g i.index = f i :=
by simp [in_index_elim, index.index]

@[simp] lemma in_index_elim_no {s : list α} (f : index s → β) (g : β) (i : ℕ)
  (h : ¬∃ (i' : index s), i'.index = i) : in_index_elim f g i = g :=
by simp [in_index_elim, λ h', h ⟨⟨i, h'⟩, rfl⟩]

lemma to_none_or_lt_id_in_index_elim_yes_none {s : list α} (f : index s → option ℕ)
  (h : ∀ (i : index s), with_bot.has_lt.lt (f i) i.index) :
  to_none_or_lt_id (in_index_elim f none) :=
begin
  intro i,
  rw in_index_elim,
  split_ifs with h',
  { exact h ⟨i, h'⟩ },
  { exact with_bot.bot_lt_coe i }
end

lemma not_map_is_some_and_lt_same {s : list α} (f : index s → option ℕ+) (i : index s) :
  i.index ∉ ((finset.image index.index $ finset.univ.filter
    (λ j : index s, option.cases_on (prod.mk <$> f j <*> f i) false (function.uncurry (<)))) : set ℕ) :=
begin
  dsimp,
  simp,
  intros j hj,
  contrapose! hj,
  replace hj := fin.eq_of_veq hj,
  rw hj,
  cases f i; dsimp [(<*>)],
  { exact not_false },
  { exact irrefl _ }
end

def index₂ (m : list (list α)) : Type := Σ (i : index m), index $ index.val i

def index₂.index {m : list (list α)} (q : index₂ m) : ℕ × ℕ := (q.fst.index, q.snd.index)

def index₂.val {m : list (list α)} (q : index₂ m) : α := q.snd.val

lemma index₂.val_mem {m : list (list α)} (q : index₂ m) : ∃ (c ∈ m), q.val ∈ c :=
⟨q.fst.val, index.val_mem _, index.val_mem _⟩

instance (m : list (list α)) : fintype (index₂ m) := sigma.fintype _

def pairable (s : list α) (t : list β) : Prop := s.length = t.length

instance (s : list α) (t : list β) : decidable $ pairable s t := nat.decidable_eq _ _

lemma pairable.def {s : list α} {t : list β} : pairable s t → s.length = t.length := id

lemma pairable.symm {s : list α} {t : list β} : pairable s t → pairable t s := symm

lemma pairable.trans {s : list α} {t : list β} {u : list γ} :
  pairable s t → pairable t u → pairable s u := eq.trans

def pairable.transfer {s : list α} {t : list β} (h : pairable s t) (i : index s) : index t :=
⟨i.index, lt_of_lt_of_eq i.property h⟩

@[simp] lemma pairable.index_transfer {s : list α} {t : list β} (h : pairable s t) (i : index s) :
  (h.transfer i).index = i.index := rfl

def pairable₂ (m₁ : list (list α)) (m₂ : list (list β)) : Prop :=
∃ (h : pairable m₁ m₂), ∀ (i : index m₁), pairable i.val (h.transfer i).val

instance (m₁ : list (list α)) (m₂ : list (list β)) : decidable $ pairable₂ m₁ m₂ := exists_prop_decidable _

lemma pairable₂.symm {m₁ : list (list α)} {m₂ : list (list β)} : pairable₂ m₁ m₂ → pairable₂ m₂ m₁ :=
assume h, ⟨h.fst.symm, λ i, (h.snd (h.fst.symm.transfer i)).symm⟩

def pairable₂.transfer {m₁ : list (list α)} {m₂ : list (list β)}
  (h : pairable₂ m₁ m₂) (q : index₂ m₁) : index₂ m₂ :=
⟨h.fst.transfer q.fst, (h.snd q.fst).transfer q.snd⟩

@[simp] lemma pairable₂.index₂_fst_transfer {m₁ : list (list α)} {m₂ : list (list β)}
  (h : pairable₂ m₁ m₂) (q : index₂ m₁) : (h.transfer q).fst.index = q.fst.index := rfl

@[simp] lemma pairable₂.index₂_snd_transfer {m₁ : list (list α)} {m₂ : list (list β)}
  (h : pairable₂ m₁ m₂) (q : index₂ m₁) : (h.transfer q).snd.index = q.snd.index := rfl


@[simp] lemma option.seq_none_right {f : option (α → β)} : f <*> none = none :=
by { cases f; refl }

end intro


section types

/-- 𝕊 -/
def value_list : Type :=
{s : list ℕ+ // if h : 1 ≤ s.length then s.nth_le 0 h = 1 else true}

/-- ^𝕊 -/
def parent_list : Type :=
{t : list (option ℕ) // ∀ (i : index t), with_bot.has_lt.lt i.val i.index}

/-- 𝕊⁽²⁾ -/
structure value_parent_list_pair :=
(values : value_list)
(parents : parent_list)
(pairable : pairable values.val parents.val)

/-- 𝕊⁽²⁾* = {x : 𝕊⁽²⁾ // x.is_orphanless} -/
def value_parent_list_pair.is_orphanless (x : value_parent_list_pair) : Prop :=
∀ (i : index x.values.val), 1 < i.val.val → (x.pairable.transfer i).val.is_some

instance : decidable_pred value_parent_list_pair.is_orphanless :=
λ x, fintype.decidable_forall_fintype

example : {x : value_parent_list_pair // value_parent_list_pair.is_orphanless x} :=
let s : list ℕ+ := [1, 3, 4], t := [none, some 0, some 1] in
  ⟨⟨⟨s, dec_trivial⟩, ⟨t, dec_trivial⟩, dec_trivial⟩, dec_trivial⟩

/-- 𝕄ᵥ -/
def value_mountain : Type :=
{V : list (list ℕ+) // ∀ (c ∈ V), c ≠ []}

/-- 𝕄ₚ⁻ -/
def parent_mountain : Type :=
{P : list (list (option ℕ)) // ∀ (c ∈ P), c ≠ []}

/-- 𝕄ₚ = {P : 𝕄ₚ⁻ // P.is_coherent} -/
def parent_mountain.is_coherent (P : parent_mountain) : Prop :=
∀ (q : index₂ P.val), let i := q.fst.index, j := q.snd.index in
  (q.val = none ↔ j = q.fst.val.length - 1) ∧
  with_bot.has_lt.lt q.val i ∧
  option.elim true (λ p, ∃ (q' : index₂ P.val), q'.index = (p, j)) q.val

instance : decidable_pred parent_mountain.is_coherent :=
λ P, fintype.decidable_forall_fintype

def parent_mountain.is_coherent.index_parent_of_is_some {P : parent_mountain} (hP : P.is_coherent)
  {q : index₂ P.val} (hq : q.val.is_some) :
  {q' : index₂ P.val // let i := q.fst.index, j := q.snd.index in q'.index = (option.get hq, j)} :=
⟨⟨⟨option.get hq, begin
  have h := (hP q).right.right,
  rw ← option.some_get hq at h,
  rcases h with ⟨⟨q'₁, q'₂⟩, hq'⟩,
  simp [index₂.index] at hq',
  obtain ⟨hq'₁, hq'₂⟩ := hq',
  exact lt_of_eq_of_lt hq'₁.symm q'₁.property
end⟩,
  ⟨q.snd.index, begin
  have h := (hP q).right.right,
  rw ← option.some_get hq at h,
  rcases h with ⟨⟨q'₁, q'₂⟩, hq'⟩,
  simp [index₂.index] at hq',
  obtain ⟨hq'₁, hq'₂⟩ := hq',
  refine lt_of_eq_of_lt hq'₂.symm (lt_of_lt_of_eq q'₂.property _),
  cases hi₂ : q'₁ with i hi₁,
  congr,
  rw hi₂ at hq'₁,
  exact hq'₁
end⟩⟩, rfl⟩

def parent_mountain.is_coherent.index_above_of_is_some {P : parent_mountain} (hP : P.is_coherent)
  {q : index₂ P.val} (hq : q.val.is_some) :
  {q' : index₂ P.val // let i := q.fst.index, j := q.snd.index in q'.index = (i, j + 1)} :=
⟨⟨q.fst, ⟨q.snd.index + 1, begin
  have h := (not_iff_not.mpr (hP q).left).mp (option.ne_none_iff_is_some.mpr hq),
  rw lt_iff_le_and_ne,
  split,
  { exact nat.succ_le_of_lt q.snd.property },
  { rw [← ne.def, ← nat.succ_ne_succ] at h,
    rw ← nat.sub_add_cancel (list.length_pos_of_ne_nil (P.property _ (index.val_mem _))),
    exact h }
end⟩⟩, rfl⟩

/-- 𝕄⁻ -/
structure mountain :=
(values : value_mountain)
(parents : parent_mountain)
(pairable : pairable₂ values.val parents.val)

/-- 𝕄* = {x : mountain // x.parents.is_coherent ∧ x.is_orphanless} -/
def mountain.is_orphanless (x : mountain) : Prop :=
∀ (i : index x.values.val),
  1 < (@index₂.val _ x.values.val ⟨i, ⟨0,
    list.length_pos_of_ne_nil (x.values.property _ (index.val_mem _))⟩⟩).val → 
  (@index₂.val _ x.parents.val ⟨x.pairable.fst.transfer i, ⟨0,
    list.length_pos_of_ne_nil (x.parents.property _ (index.val_mem _))⟩⟩).is_some

def mountain.is_cross_coherent (x : mountain) : Prop :=
∃ (hP : x.parents.is_coherent), ∀ {q : index₂ x.parents.val} (hq : q.val.is_some),
  (x.pairable.symm.transfer (hP.index_above_of_is_some hq).val).val =
  (x.pairable.symm.transfer q).val - (x.pairable.symm.transfer (hP.index_parent_of_is_some hq).val).val

/-- 𝕄** = {x : mountain // x.is_coherent} -/
def mountain.is_coherent (x : mountain) : Prop :=
x.is_orphanless ∧ x.is_cross_coherent

instance : decidable_pred mountain.is_orphanless :=
λ x, fintype.decidable_forall_fintype

end types


section build

structure row_builder (x : value_parent_list_pair) : Type :=
(value : index x.values.val → option ℕ+)
(parent : index x.values.val → option ℕ)
(to_none_or_lt_id_parent : to_none_or_lt_id (in_index_elim parent none))
(parent_as_index :
  Π {i : index x.values.val} (h : (parent i).is_some),
    {p : index x.values.val // p.index = @option.get _ (parent i) h})
(parent_spec :
  ∀ {i : index x.values.val} (h : (parent i).is_some), let p := (@parent_as_index i h).val in
    (option.cases_on (prod.mk <$> value p <*> value i) false (function.uncurry (<)) : Prop))
(value_is_some_of_parent_is_some :
  ∀ {i : index x.values.val}, (parent i).is_some → (value i).is_some)
(value_parent_is_some_of_parent_is_some :
  ∀ {i : index x.values.val} (h : (parent i).is_some), let p := (@parent_as_index i h).val in
    (value p).is_some)

def build_row_builder (x : value_parent_list_pair)
  (value : index x.values.val → option ℕ+)
  (parent_candidate_next : index x.values.val → option ℕ)
  (to_none_or_lt_id_parent_candidate_next : to_none_or_lt_id (in_index_elim parent_candidate_next none)) :
  row_builder x :=
let parent : index x.values.val → option ℕ := λ i,
    @find_iterate_of_to_none_or_lt_id
      (in_index_elim parent_candidate_next none)
      to_none_or_lt_id_parent_candidate_next
      ((finset.univ.filter (λ (p : index x.values.val),
        option.cases_on (prod.mk <$> value p <*> value i) false (function.uncurry (<)))).map
          ⟨index.index, fin.val_injective⟩)
      (by apply_instance) i.index in
have to_none_or_lt_id_parent : to_none_or_lt_id (in_index_elim parent none) :=
  begin
    apply to_none_or_lt_id_in_index_elim_yes_none,
    intro i,
    apply to_none_or_lt_id_find_iterate_of_nin,
    simp,
    intro k,
    contrapose!,
    intro hk,
    rw fin.eq_of_veq hk,
    cases (value i),
    { exact not_false },
    { dsimp, exact irrefl _ }
  end,
let parent_as_index :
  Π {i : index x.values.val} (h : (parent i).is_some),
    {p : index x.values.val // p.index = @option.get _ (parent i) h} := λ i h,
  ⟨⟨@option.get _ (parent i) h,
    begin
      cases i with i hi,
      have parent_i := to_none_or_lt_id_parent i,
      simp [in_index_elim, hi] at parent_i,
      rw @fin.eq_of_veq _ ⟨i, _⟩ ⟨i, hi⟩ rfl at parent_i,
      obtain ⟨p, hp⟩ := option.is_some_iff_exists.mp h,
      simp [hp] at parent_i ⊢,
      exact lt_trans (with_bot.coe_lt_coe.mp parent_i) hi
    end⟩, rfl⟩ in
have parent_spec :
  ∀ {i : index x.values.val} (h : (parent i).is_some), let p := (@parent_as_index i h).val in
    (option.cases_on (prod.mk <$> value p <*> value i) false (function.uncurry (<)) : Prop) :=
  begin
    intros i h,
    obtain ⟨k, hk⟩ := option.is_some_iff_exists.mp h,
    have hp : (@parent_as_index i h).val.index = k,
      by simp only [index.index, option.get_some, eq_self_iff_true, hk],
    have spec : option.elim true _ (parent i) := find_iterate_spec _ _ _,
    rw [hk, option.elim, ← @set.mem_def _ k (_ : finset ℕ)] at spec,
    simp at spec,
    rcases spec with ⟨p', hp'₁, hp'₂⟩,
    rw fin.eq_of_veq (hp.trans hp'₂.symm),
    exact hp'₁
  end,
have value_is_some_of_parent_is_some :
  ∀ {i : index x.values.val}, (parent i).is_some → (value i).is_some :=
  begin
    intros i h,
    specialize parent_spec h,
    contrapose parent_spec with H,
    rw option.not_is_some_iff_eq_none at H,
    delta,
    rw [H, option.seq_none_right],
    tauto
  end,
have value_parent_is_some_of_parent_is_some :
  ∀ {i : index x.values.val} (h : (parent i).is_some), let p := (@parent_as_index i h).val in
    (value p).is_some :=
  begin
    intros i h,
    specialize parent_spec h,
    contrapose parent_spec with H,
    rw option.not_is_some_iff_eq_none at H,
    delta,
    rw H,
    tauto
  end,
{ value := @value,
  parent := @parent,
  to_none_or_lt_id_parent := @to_none_or_lt_id_parent,
  parent_as_index := @parent_as_index,
  parent_spec := @parent_spec,
  value_is_some_of_parent_is_some := @value_is_some_of_parent_is_some,
  value_parent_is_some_of_parent_is_some := @value_parent_is_some_of_parent_is_some }

def mountain_builder (x : value_parent_list_pair) : ℕ → row_builder x
| 0 := build_row_builder x (some ∘ index.val) (index.val ∘ x.pairable.transfer)
  begin
    apply to_none_or_lt_id_in_index_elim_yes_none,
    intro,
    rw ← pairable.index_transfer x.pairable _,
    exact x.parents.property _
  end
| (j + 1) := let prev := mountain_builder j in
  build_row_builder x
    (λ i, if h : (prev.parent i).is_some
      then let p := prev.parent_as_index /- i -/ h in some $
        @option.get _ (prev.value i) (prev.value_is_some_of_parent_is_some h) -
        @option.get _ (prev.value p) (prev.value_parent_is_some_of_parent_is_some h)
      else none)
    prev.parent prev.to_none_or_lt_id_parent

def value (x : value_parent_list_pair) (i : index x.values.val) (j : ℕ) : option ℕ+ :=
(mountain_builder x j).value i

def parent (x : value_parent_list_pair) (i : index x.values.val) (j : ℕ) : option ℕ :=
(mountain_builder x j).parent i

lemma to_none_or_lt_id_parent (x : value_parent_list_pair) (j : ℕ) :
  to_none_or_lt_id (in_index_elim (λ i, parent x i j) none) :=
(mountain_builder x j).to_none_or_lt_id_parent

def parent_as_index {x : value_parent_list_pair} {i : index x.values.val} {j : ℕ} (h : (parent x i j).is_some) :
  {p : index x.values.val // p.index = @option.get _ (parent x i j) h} :=
(mountain_builder x j).parent_as_index h

lemma parent_spec {x : value_parent_list_pair} {i : index x.values.val} {j : ℕ}
  (h : (parent x i j).is_some) : let p := (@parent_as_index x i j h).val in
  (option.cases_on (prod.mk <$> value x p j <*> value x i j) false (function.uncurry (<)) : Prop) :=
(mountain_builder x j).parent_spec h

lemma value_is_some_of_parent_is_some {x : value_parent_list_pair} {i : index x.values.val} {j : ℕ} :
  (parent x i j).is_some → (value x i j).is_some :=
(mountain_builder x j).value_is_some_of_parent_is_some

lemma value_parent_is_some_of_parent_is_some {x : value_parent_list_pair} {i : index x.values.val} {j : ℕ}
  (h : (parent x i j).is_some) : let p := (@parent_as_index x i j h).val in
  (value x p j).is_some :=
(mountain_builder x j).value_parent_is_some_of_parent_is_some h

lemma value_parent_lt_value {x : value_parent_list_pair} {i : index x.values.val} {j : ℕ}
  (h : (parent x i j).is_some) : let p := (@parent_as_index x i j h).val in
  @option.get _ (value x p j) (value_parent_is_some_of_parent_is_some h) <
  @option.get _ (value x i j) (value_is_some_of_parent_is_some h) :=
begin
  have spec := parent_spec h,
  obtain ⟨m, hm⟩ := option.is_some_iff_exists.mp (value_parent_is_some_of_parent_is_some h),
  obtain ⟨n, hn⟩ := option.is_some_iff_exists.mp (value_is_some_of_parent_is_some h),
  simp only [option.get_some, parent, hm, hn],
  delta at spec,
  rw [hm, hn] at spec,
  exact spec
end

lemma parent_of_value_eq_none {x : value_parent_list_pair} {i : index x.values.val} {j : ℕ} :
  value x i j = none → parent x i j = none :=
by { contrapose, simp_rw [← ne.def, option.ne_none_iff_is_some], exact value_is_some_of_parent_is_some }

@[simp] lemma value_zero (x : value_parent_list_pair) (i : index x.values.val) :
  value x i 0 = some i.val := rfl

@[simp] lemma value_succ (x : value_parent_list_pair) (i : index x.values.val) (j : ℕ) :
  value x i (j + 1) = if h : (parent x i j).is_some
    then let p := (@parent_as_index x i j h).val in some $
      @option.get _ (value x i j) (value_is_some_of_parent_is_some h) -
      @option.get _ (value x p j) (value_parent_is_some_of_parent_is_some h)
    else none := rfl

@[simp] lemma parent_zero (x : value_parent_list_pair) (i : index x.values.val) :
  parent x i 0 = @find_iterate_of_to_none_or_lt_id
    (in_index_elim (index.val ∘ x.pairable.transfer) none)
    begin
      apply to_none_or_lt_id_in_index_elim_yes_none,
      intro,
      rw ← pairable.index_transfer x.pairable _,
      exact x.parents.property _
    end
    ((finset.univ.filter (λ (p : index x.values.val),
      option.cases_on (prod.mk <$> value x p 0 <*> value x i 0) false (function.uncurry (<)))).map
        ⟨index.index, fin.val_injective⟩)
    (by apply_instance) i.index := rfl

@[simp] lemma parent_succ (x : value_parent_list_pair) (i : index x.values.val) (j : ℕ) :
  parent x i (j + 1) = @find_iterate_of_to_none_or_lt_id
    (in_index_elim (λ p, parent x p j) none)
    (to_none_or_lt_id_parent x j)
    ((finset.univ.filter (λ (p : index x.values.val),
      option.cases_on (prod.mk <$> value x p (j + 1) <*> value x i (j + 1)) false (function.uncurry (<)))).map
        ⟨index.index, fin.val_injective⟩)
    (by apply_instance) i.index := rfl

lemma value_succ_is_some_iff_parent_is_some {x : value_parent_list_pair} {i : index x.values.val} {j : ℕ} :
  (value x i (j + 1)).is_some ↔ (parent x i j).is_some :=
begin
  split,
  { contrapose,
    intro H,
    simp [H] },
  { intro h,
    simp [h] }
end

lemma value_succ_eq_none_iff_parent_eq_none {x : value_parent_list_pair} {i : index x.values.val} {j : ℕ} :
  value x i (j + 1) = none ↔ parent x i j = none :=
begin
  rw ← not_iff_not,
  simp_rw [← ne.def, option.ne_none_iff_is_some],
  exact value_succ_is_some_iff_parent_is_some
end

lemma val_value_above_eq_of_parent_is_some {x : value_parent_list_pair}
  {i : index x.values.val} {j : ℕ} (h : (parent x i j).is_some) :
  (@option.get _ (value x i (j + 1)) (value_succ_is_some_iff_parent_is_some.mpr h)).val =
  let p := (@parent_as_index x i j h).val in
  (@option.get _ (value x i j) (value_is_some_of_parent_is_some h)).val -
  (@option.get _ (value x p j) (value_parent_is_some_of_parent_is_some h)).val :=
begin
  obtain ⟨⟨vt, vt_pos⟩, hvt⟩ := option.is_some_iff_exists.mp (value_is_some_of_parent_is_some h),
  obtain ⟨⟨vp, vp_pos⟩, hvp⟩ := option.is_some_iff_exists.mp (value_parent_is_some_of_parent_is_some h),
  have vp_lt_vt := value_parent_lt_value h,
  simp [hvt, hvp, value_succ, -subtype.val_eq_coe] at vp_lt_vt ⊢,
  simp [option.get_some, h, pnat.sub_coe, vp_lt_vt]
end

lemma value_above_lt_value_of_parent_is_some {x : value_parent_list_pair}
  {i : index x.values.val} {j : ℕ} (h : (parent x i j).is_some) :
  (@option.get _ (value x i (j + 1)) (value_succ_is_some_iff_parent_is_some.mpr h)).val <
  (@option.get _ (value x i j) (value_is_some_of_parent_is_some h)).val :=
begin
  rw val_value_above_eq_of_parent_is_some,
  obtain ⟨⟨vt, vt_pos⟩, hvt⟩ := option.is_some_iff_exists.mp (value_is_some_of_parent_is_some h),
  obtain ⟨⟨vp, vp_pos⟩, hvp⟩ := option.is_some_iff_exists.mp (value_parent_is_some_of_parent_is_some h),
  simp [hvt, hvp, value_succ, -subtype.val_eq_coe],
  exact nat.sub_lt vt_pos vp_pos
end

def height_finite (x : value_parent_list_pair) (i : index x.values.val) : ∃ (j : ℕ), value x i j = none :=
begin
  refine @well_founded.induction_bot (with_bot ℕ+) (<)
    (with_bot.well_founded_lt is_well_founded.wf) _ _
    (λ r, ∃ (j : ℕ), value x i j = r) _ ⟨0, rfl⟩,
  dsimp,
  intros a ha IH,
  rcases IH with ⟨j, rfl⟩,
  refine ⟨_, _, j + 1, rfl⟩,
  have value_succ_eq := value_succ x i j,
  split_ifs at value_succ_eq with h,
  { obtain ⟨⟨vt, vt_pos⟩, hvt⟩ := option.is_some_iff_exists.mp (value_is_some_of_parent_is_some h),
    obtain ⟨⟨va, va_pos⟩, hva⟩ := option.is_some_iff_exists.mp (value_succ_is_some_iff_parent_is_some.mpr h),
    have va_lt_vt := value_above_lt_value_of_parent_is_some h,
    simp * at va_lt_vt ⊢,
    exact va_lt_vt },
  { rw value_succ_eq,
    exact ne.bot_lt ha }
end

def height (x : value_parent_list_pair) (i : index x.values.val) : ℕ :=
nat.find (height_finite x i)

lemma height_spec (x : value_parent_list_pair) (i : index x.values.val) : value x i (height x i) = none :=
nat.find_spec (height_finite x i)

lemma height_min {x : value_parent_list_pair} {i : index x.values.val} {j : ℕ} :
  j < height x i → value x i j ≠ none :=
nat.find_min (height_finite x i)

lemma height_pos (x : value_parent_list_pair) (i : index x.values.val) : 0 < height x i :=
begin
  by_contra H,
  simp at H,
  have := height_spec x i,
  rw H at this,
  contradiction
end

lemma value_eq_none_of_ge_height {x : value_parent_list_pair} {i : index x.values.val} {j : ℕ}
  (h : height x i ≤ j) : value x i j = none :=
begin
  refine nat.le_induction (height_spec x i) _ j h,
  simp,
  intros j hj IH H,
  exact absurd (parent_of_value_eq_none IH) (option.ne_none_iff_is_some.mpr H)
end

lemma value_is_some_of_lt_height {x : value_parent_list_pair} {i : index x.values.val} {j : ℕ} :
  j < height x i → (value x i j).is_some :=
option.ne_none_iff_is_some.mp ∘ height_min

lemma value_is_some_iff_lt_height {x : value_parent_list_pair} {i : index x.values.val} {j : ℕ} :
  (value x i j).is_some ↔ j < height x i :=
⟨begin
    contrapose,
    simp,
    intro H,
    exact option.is_none_iff_eq_none.mpr (value_eq_none_of_ge_height H)
  end,
  value_is_some_of_lt_height⟩

lemma value_eq_none_iff_ge_height {x : value_parent_list_pair} {i : index x.values.val} {j : ℕ} :
  value x i j = none ↔ height x i ≤ j :=
begin
  rw [← not_iff_not, ← ne.def, option.ne_none_iff_is_some, not_le],
  exact value_is_some_iff_lt_height
end

def build_mountain (x : value_parent_list_pair) : mountain :=
{ values := ⟨(λ (i : index x.values.val),
    (λ (j : fin (height x i)),
      @option.get _ (value x i j.val) (value_is_some_of_lt_height j.property)) <$>
      list.fin_range (height x i)) <$>
    list.fin_range x.values.val.length,
    begin
      intros _ h,
      simp at h,
      cases h with i h,
      rw [← h, ne.def, list.map_eq_nil, list.fin_range_eq_nil, ← ne.def],
      exact ne_of_gt (height_pos x i)
    end⟩,
  parents := ⟨(λ (i : index x.values.val),
    (λ (j : fin (height x i)),
      parent x i j.val) <$>
      list.fin_range (height x i)) <$>
    list.fin_range x.values.val.length,
    begin
      intros _ h,
      simp at h,
      cases h with i h,
      rw [← h, ne.def, list.map_eq_nil, list.fin_range_eq_nil, ← ne.def],
      exact ne_of_gt (height_pos x i)
    end⟩,
  pairable := by simp [pairable₂, pairable, index.val] }

lemma mountain_length_eq (x : value_parent_list_pair) :
  (build_mountain x).values.val.length = x.values.val.length := by simp [build_mountain]

lemma mountain_height_eq (x : value_parent_list_pair) (i : index (build_mountain x).values.val) :
  i.val.length = height x (pairable.transfer (mountain_length_eq x) i) :=
by simp [pairable.transfer, index.val, build_mountain, index.index]

lemma mountain_height_eq' (x : value_parent_list_pair) (i : index x.values.val) :
  (pairable.transfer (mountain_length_eq x).symm i).val.length = height x i :=
by simp [mountain_height_eq, pairable.transfer, build_mountain, index.index]

lemma mountain_value_at_index_eq_value (x : value_parent_list_pair) (q : index₂ (build_mountain x).values.val) :
  q.val = @option.get _
    (value x (pairable.transfer (mountain_length_eq x) q.fst) q.snd.index)
    begin
      apply value_is_some_of_lt_height,
      rw ← mountain_height_eq,
      exact q.snd.property,
    end :=
by simp [pairable.transfer, index₂.val, index.val, build_mountain, index.index]

lemma mountain_parent_at_index_eq_parent (x : value_parent_list_pair) (q : index₂ (build_mountain x).parents.val) :
  q.val = parent x
    (pairable.transfer ((build_mountain x).pairable.fst.symm.trans (mountain_length_eq x)) q.fst)
    q.snd.index :=
by simp [pairable.transfer, index₂.val, index.val, build_mountain, index.index]

theorem build_mountain_parents_is_coherent (x : value_parent_list_pair) :
  (build_mountain x).parents.is_coherent :=
begin
  rintro ⟨i, j⟩,
  dsimp,
  refine ⟨_, _, _⟩,
  { rw [mountain_parent_at_index_eq_parent,
      ← value_succ_eq_none_iff_parent_eq_none,
      value_eq_none_iff_ge_height],
    simp [pairable.transfer],
    rw nat.le_add_one_iff,
    conv in (height _ _ = j.index + 1)
    { rw ← nat.sub_add_cancel (nat.succ_le_of_lt (height_pos _ _)) },
    have iheight := eq.trans
      ((build_mountain x).pairable.snd _).symm
      (mountain_height_eq _ ((build_mountain x).pairable.fst.symm.transfer i)),
    simp [pairable.transfer, index.index] at iheight,
    conv at iheight in (coe i) { change i.index },
    rw [eq_comm, iheight, add_left_inj, or_iff_right_iff_imp],
    rw ← iheight,
    intro h,
    exact absurd j.property (not_lt_of_le h) },
  { refine lt_of_eq_of_lt _ (to_none_or_lt_id_parent x j.index i.index),
    symmetry,
    simp only [in_index_elim],
    rw [dite_eq_iff', and_iff_left],
    swap,
    { intro h,
      refine absurd (lt_of_lt_of_eq i.property _) h,
      exact (build_mountain x).pairable.fst.symm.trans (mountain_length_eq x) },
    intro,
    rw mountain_parent_at_index_eq_parent,
    refl },
  { cases h : index₂.val _ with k,
    { triv },
    { rw mountain_parent_at_index_eq_parent at h,
      let q := (parent_as_index (option.is_some_iff_exists.mpr ⟨k, h⟩)),
      let p := q.val,
      refine ⟨⟨pairable.transfer
            ((mountain_length_eq x).symm.trans (build_mountain x).pairable.fst) p,
          ⟨j.index, _⟩⟩, _⟩,
      { apply eq.subst ((mountain_height_eq' x _).symm.trans ((build_mountain x).pairable.snd _)),
        rw ← value_is_some_iff_lt_height,
        exact value_parent_is_some_of_parent_is_some (option.is_some_iff_exists.mpr ⟨k, h⟩) },
      { have hp := q.property,
        simp only [h, option.get_some] at hp,
        exact prod.ext hp rfl } } }
end

theorem build_mountain_orphanless_is_orphanless (x : value_parent_list_pair) (h : x.is_orphanless) :
  (build_mountain x).is_orphanless :=
begin
  rintro ⟨i, hi⟩,
  simp [mountain_value_at_index_eq_value, mountain_parent_at_index_eq_parent,
    pairable.transfer, index.index, find_iterate_of_to_none_or_lt_id],
  intro value_gt_one,
  have i_has_parent_candidate := h _ value_gt_one,
  simp [pairable.transfer, index.index] at i_has_parent_candidate,
  rw find_iterate_is_some_iff,
  dsimp,
  simp,
  revert i_has_parent_candidate,
  rename [i i₀, hi hi₀, value_gt_one value₀_gt_one],
  let i₀_on_mv : index _ := ⟨i₀, hi₀⟩,
  let i₀_on_lv : index _ := pairable.transfer (mountain_length_eq x) i₀_on_mv,
  refine @nat.strong_induction_on
    (λ i, ∀ (hi : _ < _), _ < _ → option.is_some _ →
      ∃ (k : ℕ) (h : option.is_some _) (p : index _), _ < index.val ⟨i₀, i₀_on_lv.property⟩ ∧ _)
    i₀ _ hi₀ value₀_gt_one,
  intros i IH hi value_gt_one i_has_parent_candidate,
  let i_on_mv : index _ := ⟨i, hi⟩,
  let i_on_lv : index _ := pairable.transfer (mountain_length_eq x) i_on_mv,
  let i_on_lp : index _ := pairable.transfer ((mountain_length_eq x).trans x.pairable) i_on_mv,
  induction i using nat.strong_induction_on with i IH,
  let p := option.get i_has_parent_candidate,
  have hp := option.some_get i_has_parent_candidate,
  have p_lt_i : p < i,
  { have := x.parents.property i_on_lp,
    simp [i_on_lp, pairable.transfer, index.index] at this,
    rw ← hp at this,
    exact with_bot.some_lt_some.mp this },
  have p_lt_length : p < x.values.val.length,
    from p_lt_i.trans (lt_of_lt_of_eq hi (mountain_length_eq x)),
  let p' : index _ := ⟨p, p_lt_length⟩,
  by_cases h' : p'.val < i₀_on_lv.val,
  work_on_goal 1
  { suffices,
    { refine ⟨1, _, _⟩,
      { rw option.is_some_iff_exists,
        exact ⟨p, this⟩ },
      { refine ⟨p', ⟨h', _⟩⟩,
        rw [← option.some_inj, option.some_get],
        exact this.symm } } },
  work_on_goal 2
  { rw not_lt at h',
    have value_parent_gt_one := lt_of_lt_of_le value₀_gt_one h',
    have p_has_parent_candidate := h _ value_parent_gt_one,
    specialize IH p p_lt_i (lt_of_lt_of_eq p_lt_length (mountain_length_eq x).symm)
      value_parent_gt_one p_has_parent_candidate,
    rcases IH with ⟨k, hk, ⟨tp, ⟨htp₁, htp₂⟩⟩⟩,
    suffices,
    { refine ⟨k + 1, _, _⟩,
      { rw option.is_some_iff_exists,
        exact ⟨tp.index, this⟩ },
      { refine ⟨tp, ⟨htp₁, _⟩⟩,
        rw [← option.some_inj, option.some_get],
        exact this.symm } },
    rw [← option.some_inj, option.some_get] at htp₂,
    rw [function.iterate_succ_apply, htp₂],
    congr
  },
  all_goals
  { have := i_on_lv.property,
    simp [i_on_lv, i_on_mv, pairable.transfer, index.index] at this,
    simp [flip, in_index_elim, this],
    refl }
end

theorem build_mountain_orphanless_is_cross_coherent (x : value_parent_list_pair) (h : x.is_orphanless) :
  (build_mountain x).is_cross_coherent :=
begin
  have hP := build_mountain_parents_is_coherent x,
  use hP,
  rintros ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ hq,
  dsimp [pairable₂.transfer, pairable.transfer, index.index,  parent_mountain.is_coherent.index_above_of_is_some, parent_mountain.is_coherent.index_parent_of_is_some],
  simp [mountain_parent_at_index_eq_parent, pairable.transfer, index.index] at hq,
  obtain ⟨⟨vt, vt_pos⟩, hvt⟩ := option.is_some_iff_exists.mp (value_is_some_of_parent_is_some hq),
  obtain ⟨⟨vp, vp_pos⟩, hvp⟩ := option.is_some_iff_exists.mp (value_parent_is_some_of_parent_is_some hq),
  obtain ⟨⟨va, va_pos⟩, hva⟩ := option.is_some_iff_exists.mp (value_succ_is_some_iff_parent_is_some.mpr hq),
  have vp_lt_vt := value_parent_lt_value hq,
  simp [hvt, hvp, value_succ, -subtype.val_eq_coe] at vp_lt_vt ⊢,
  have va_eq := val_value_above_eq_of_parent_is_some hq,
  simp [hvt, hvp, hva, -subtype.val_eq_coe] at va_eq ⊢,
  obtain ⟨p, hp⟩ := option.is_some_iff_exists.mp hq,
  simp only [mountain_value_at_index_eq_value, mountain_parent_at_index_eq_parent, pairable.transfer, index.index, hp, option.get_some],
  obtain ⟨⟨p', hp'₁⟩, hp'₂⟩ := parent_as_index hq,
  intro hvp,
  simp only [hp, option.get_some, index.index] at hp'₂,
  simp only [parent_as_index, hp, option.get_some, subtype.val, hp'₂] at hvp,
  simp [hvt, hvp, hva, va_eq, ← pnat.coe_inj, pnat.sub_coe, vp_lt_vt]
end

theorem build_mountain_orphanless_is_coherent (x : value_parent_list_pair) (h : x.is_orphanless) :
  (build_mountain x).is_coherent :=
⟨build_mountain_orphanless_is_orphanless x h, build_mountain_orphanless_is_cross_coherent x h⟩

end build

end ysequence