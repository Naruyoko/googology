import
  algebra.order.positive.ring
  control.monad.basic
  control.fix
  data.fintype.sigma
  data.list.basic
  data.pnat.basic
  order.iterate

namespace ysequence

section intro
variables {α β : Type}

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
∀ x, ∃ k, (flip bind f)^[k] x = none

lemma iterate_eventually_none_or_mem_of_iterate_eventually_none {f : α → option α} (hf : iterate_eventually_none f)
  (p : set α) (x : α) : ∃ k, option.elim true p $ (flip bind f)^[k] $ some x :=
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

def find_iterate_of_iterate_eventually_none {f : α → option α} (hf : iterate_eventually_none f)
  {p : set α} (decidable_p : decidable_pred p) : α → option α :=
λ x, (flip bind f)^[find_index_iterate_of_iterate_eventually_none hf decidable_p x] $ some x

lemma find_iterate_spec {f : α → option α} (hf : iterate_eventually_none f)
  {p : set α} (decidable_p : decidable_pred p) (x : α) :
  option.elim true p $ find_iterate_of_iterate_eventually_none hf decidable_p x :=
find_index_iterate_spec _ _ _

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
∀ n, option.elim true (λ m, m < n) (f n)

theorem iterate_eventually_none_of_to_none_or_lt_id {f : ℕ → option ℕ} (hf : to_none_or_lt_id f) :
  iterate_eventually_none f :=
begin
  suffices : ∀ {m n}, option.elim true (λ m, m < n) m → ((flip bind f)^[n] m) = none,
  { intro n,
    cases n,
    { exact ⟨0, rfl⟩ },
    { refine ⟨n + 1, this (by simp)⟩ } },
  intros m n hmn,
  induction n with n IH generalizing m,
  { cases m,
    { refl },
    { exact absurd hmn (nat.not_lt_zero _) } },
  { rw function.iterate_succ_apply,
    apply IH,
    cases m with m,
    { assumption },
    { specialize hf m,
      have : (flip bind f $ some m) = f m := rfl,
      rw this,
      cases f m,
      { assumption },
      { exact nat.lt_of_lt_of_le hf (nat.le_of_lt_succ hmn) } } }
end

def find_iterate_of_to_none_or_lt_id {f : ℕ → option ℕ} (hf : to_none_or_lt_id f)
  {p : set ℕ} (decidable_p : decidable_pred p) : ℕ → option ℕ :=
find_iterate_of_iterate_eventually_none (iterate_eventually_none_of_to_none_or_lt_id hf) decidable_p

lemma iterate_bind_none (f : α → option α) (n : ℕ) : (flip bind f)^[n] none = none :=
flip n.rec_on (by { intros n IH, simpa only [function.iterate_succ_apply', IH] }) rfl

theorem to_none_or_lt_id_iterate_succ {f : ℕ → option ℕ} (hf : to_none_or_lt_id f) (n k : ℕ) :
  option.elim true (λ r, r < n) $ (flip bind f)^[k + 1] $ some n :=
begin
  induction k with k IH,
  { exact hf n },
  { rw function.iterate_succ_apply',
    cases ((flip bind f)^[k + 1] $ some n) with l,
    { triv },
    { specialize hf l,
      dsimp [IH, flip] at *,
      cases f l,
      { triv },
      { dsimp at *,
        exact lt_trans hf IH } } }
end

theorem to_none_or_lt_id_iterate_pos {f : ℕ → option ℕ} (hf : to_none_or_lt_id f)
  (n : ℕ) {k : ℕ} (hk : 0 < k) : option.elim true (λ r, r < n) $ (flip bind f)^[k] $ some n :=
begin
  cases k,
  { exact absurd hk dec_trivial },
  { exact to_none_or_lt_id_iterate_succ hf n k }
end

theorem to_none_or_lt_id_find_iterate_of_nin {f : ℕ → option ℕ} (hf : to_none_or_lt_id f)
  {p : set ℕ} (decidable_p : decidable_pred p) {n : ℕ} (hn : n ∉ p) :
  option.elim true (λ r, r < n) $ find_iterate_of_to_none_or_lt_id hf decidable_p n :=
to_none_or_lt_id_iterate_pos hf _ (find_index_iterate_pos_of_nin _ _ hn)

theorem to_none_or_lt_id_find_iterate_of_all_nin {f : ℕ → option ℕ} (hf : to_none_or_lt_id f)
  {g : ℕ → set ℕ} (hg₁ : ∀ n, decidable_pred $ g n) (hg₂ : ∀ n, n ∉ g n) :
  to_none_or_lt_id $ (λ n, find_iterate_of_to_none_or_lt_id hf (hg₁ n) n) :=
λ n, to_none_or_lt_id_find_iterate_of_nin hf (hg₁ n) (hg₂ n)

example :
  let p := λ n, @find_iterate_of_to_none_or_lt_id
    (λ m, nat.cases_on m none some)
    (by { intro m, cases m; simp only [nat.lt_succ_self, option.elim] })
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
  (h : ∀ (i : index s), option.elim true (λ j, j < i.index) (f i)) :
  to_none_or_lt_id (in_index_elim f none) :=
begin
  intro i,
  rw in_index_elim,
  split_ifs with h',
  { exact h ⟨i, h'⟩ },
  { triv }
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

def pairable.transfer {s : list α} {t : list β} (h : pairable s t) (i : index s) : index t :=
⟨i.index, lt_of_lt_of_eq i.property h⟩

@[simp] lemma pairable.index_transfer {s : list α} {t : list β} (h : pairable s t) (i : index s) :
  (h.transfer i).index = i.index := rfl

def pairable₂ (m₁ : list (list α)) (m₂ : list (list β)) : Prop :=
∃ (h : pairable m₁ m₂), ∀ (i : index m₁), pairable i.val (h.transfer i).val

instance (m₁ : list (list α)) (m₂ : list (list β)) : decidable $ pairable₂ m₁ m₂ := exists_prop_decidable _

lemma pairable₂.to_pairable_fst {m₁ : list (list α)} {m₂ : list (list β)} (h : pairable₂ m₁ m₂) :
  pairable m₁ m₂ :=
Exists.cases_on h (assume h₁ h₂, h₁)

lemma pairable₂.to_pairable_snd {m₁ : list (list α)} {m₂ : list (list β)} (h : pairable₂ m₁ m₂) :
  ∀ (i : index m₁), pairable i.val (h.to_pairable_fst.transfer i).val :=
Exists.cases_on h (assume h₁ h₂, h₂)

def pairable₂.transfer {m₁ : list (list α)} {m₂ : list (list β)} (h : pairable₂ m₁ m₂) (q : index₂ m₁) : index₂ m₂ :=
⟨h.to_pairable_fst.transfer q.fst, (h.to_pairable_snd q.fst).transfer q.snd⟩

@[simp] lemma pairable₂.index₂_fst_transfer {m₁ : list (list α)} {m₂ : list (list β)} (h : pairable₂ m₁ m₂) (q : index₂ m₁) :
  (h.transfer q).fst.index = q.fst.index := rfl

@[simp] lemma pairable₂.index₂_snd_transfer {m₁ : list (list α)} {m₂ : list (list β)} (h : pairable₂ m₁ m₂) (q : index₂ m₁) :
  (h.transfer q).snd.index = q.snd.index := rfl


@[simp] lemma option.seq_none_right {f : option (α → β)} : f <*> none = none :=
by { cases f; refl }

end intro


section types

/-- 𝕊 -/
def value_list : Type :=
{s : list ℕ+ // if h : 1 ≤ s.length then s.nth_le 0 h = 1 else true}

/-- ^𝕊 -/
def parent_list : Type :=
{t : list (option ℕ) // ∀ (i : index t), option.elim true (λ p, p < i.index) i.val}

/-- 𝕊⁽²⁾ -/
structure value_parent_list_pair :=
(values : value_list)
(parents : parent_list)
(pairable : pairable values.val parents.val)

/-- 𝕊⁽²⁾* -/
def lawful_value_parent_list_pair : Type :=
{x : value_parent_list_pair // ∀ (i : index x.values.val), 1 < i.val → (x.pairable.transfer i).val ≠ none}

example : lawful_value_parent_list_pair :=
let s : list ℕ+ := [1, 3, 4], t := [none, some 0, some 1] in
  ⟨⟨⟨s, dec_trivial⟩, ⟨t, dec_trivial⟩, dec_trivial⟩, dec_trivial⟩

/-- 𝕄ᵥ -/
def value_mountain : Type :=
{V : list (list ℕ+) // ∀ (c ∈ V), c ≠ []}

/-- 𝕄ₚ⁻ -/
def parent_mountain : Type :=
{P : list (list (option ℕ)) // ∀ (c ∈ P), c ≠ []}

/-- 𝕄ₚ -/
def lawful_parent_mountain : Type :=
{P : parent_mountain // ∀ (q : index₂ P.val), let i := q.fst.index, j := q.snd.index in
  (q.val = none ↔ j = q.fst.val.length - 1) ∧
  (option.elim true (λ p, p < i ∧ ∃ (q' : index₂ P.val), q.index = (p, j)) q.val)}

/-- 𝕄⁻ -/
structure mountain :=
(values : value_mountain)
(parents : parent_mountain)
(pairable : pairable₂ values.val parents.val)

/-- 𝕄 -/
structure lawful_mountain :=
(values : value_mountain)
(parents : lawful_parent_mountain)
(pairable : pairable₂ values.val parents.val.val)

def lawful_mountain.to_mountain (M : lawful_mountain) : mountain :=
⟨M.values, M.parents.val, M.pairable⟩

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
-- (parent_of_value_eq_none :
--   ∀ {i : index x.values.val}, value i = none → parent i = none)
(value_is_some_of_parent_is_some :
  ∀ {i : index x.values.val}, (parent i).is_some → (value i).is_some)
(value_parent_is_some_of_parent_is_some :
  ∀ {i : index x.values.val} (h : (parent i).is_some), let p := (@parent_as_index i h).val in
    (value p).is_some)
(value_parent_lt_value :
  ∀ {i : index x.values.val} (h : (parent i).is_some), let p := (@parent_as_index i h).val in
    @option.get _ (value p) (value_parent_is_some_of_parent_is_some h) <
    @option.get _ (value i) (value_is_some_of_parent_is_some h))

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
      specialize to_none_or_lt_id_parent i,
      simp [in_index_elim, hi] at to_none_or_lt_id_parent,
      cases parent ⟨i, hi⟩ with p,
      { contradiction },
      { exact lt_of_eq_of_lt (option.get_some _ _) (lt_trans to_none_or_lt_id_parent hi) }
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
have value_parent_lt_value :
  ∀ {i : index x.values.val} (h : (parent i).is_some), let p := (@parent_as_index i h).val in
    @option.get _ (value p) (value_parent_is_some_of_parent_is_some h) <
    @option.get _ (value i) (value_is_some_of_parent_is_some h) :=
  begin
    intros i h,
    specialize parent_spec h,
    obtain ⟨m, hm⟩ := option.is_some_iff_exists.mp (value_parent_is_some_of_parent_is_some h),
    obtain ⟨n, hn⟩ := option.is_some_iff_exists.mp (value_is_some_of_parent_is_some h),
    simp only [option.get_some, parent, hm, hn],
    delta at parent_spec,
    rw [hm, hn] at parent_spec,
    exact parent_spec
  end,
{ value := @value,
  parent := @parent,
  to_none_or_lt_id_parent := @to_none_or_lt_id_parent,
  parent_as_index := @parent_as_index,
  parent_spec := @parent_spec,
  value_is_some_of_parent_is_some := @value_is_some_of_parent_is_some,
  value_parent_is_some_of_parent_is_some := @value_parent_is_some_of_parent_is_some,
  value_parent_lt_value := @value_parent_lt_value }

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
      then let p := prev.parent_as_index /- i -/ h in some
        ⟨@option.get _ (prev.value i) (prev.value_is_some_of_parent_is_some h) -
          @option.get _ (prev.value p) (prev.value_parent_is_some_of_parent_is_some h),
          begin
            simp only [pnat.coe_lt_coe, tsub_pos_iff_lt],
            exact prev.value_parent_lt_value h
          end⟩
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
(mountain_builder x j).value_parent_lt_value h

lemma parent_of_value_eq_none {x : value_parent_list_pair} {i : index x.values.val} {j : ℕ} :
  value x i j = none → parent x i j = none :=
by { contrapose, simp_rw [← ne.def, option.ne_none_iff_is_some], exact value_is_some_of_parent_is_some }

@[simp] lemma value_zero (x : value_parent_list_pair) (i : index x.values.val) :
  value x i 0 = some i.val := rfl

@[simp] lemma value_succ (x : value_parent_list_pair) (i : index x.values.val) (j : ℕ) :
  value x i (j + 1) = if h : (parent x i j).is_some
    then let p := @parent_as_index x i j h in some
      ⟨@option.get _ (value x i j) (value_is_some_of_parent_is_some h) -
        @option.get _ (value x p j) (value_parent_is_some_of_parent_is_some h),
        begin
          simp only [pnat.coe_lt_coe, tsub_pos_iff_lt],
          exact value_parent_lt_value h
        end⟩
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

end build

end ysequence