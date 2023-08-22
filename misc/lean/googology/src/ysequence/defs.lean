import
  data.fintype.sigma
  data.nat.with_bot
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

lemma find_index_iterate_pos_of_not_mem {f : α → option α} (hf : iterate_eventually_none f)
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
  refine λ n, @is_well_founded.induction _ with_bot.has_lt.lt is_well_order.to_is_well_founded _ n _,
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

theorem to_none_or_lt_id_find_iterate_of_not_mem {f : ℕ → option ℕ} (hf : to_none_or_lt_id f)
  {p : set ℕ} (decidable_p : decidable_pred p) {n : ℕ} (hn : n ∉ p) :
  with_bot.has_lt.lt (find_iterate_of_to_none_or_lt_id hf decidable_p n : option ℕ) n :=
to_none_or_lt_id_iterate_pos hf _ (find_index_iterate_pos_of_not_mem _ _ hn)

theorem to_none_or_lt_id_find_iterate_of_all_not_mem {f : ℕ → option ℕ} (hf : to_none_or_lt_id f)
  {g : ℕ → set ℕ} (hg₁ : ∀ n, decidable_pred $ g n) (hg₂ : ∀ n, n ∉ g n) :
  to_none_or_lt_id (λ n, find_iterate_of_to_none_or_lt_id hf (hg₁ n) n) :=
λ n, to_none_or_lt_id_find_iterate_of_not_mem hf (hg₁ n) (hg₂ n)

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
  apply to_none_or_lt_id_find_iterate_of_all_not_mem,
  intro n,
  simp [(∈)],
  exact not_and_not_right.mpr (congr_fun rfl)
end⟩


def index (s : list α) : Type := fin s.length

def index.index {s : list α} (i :index s) : ℕ := i.val

def index.val {s : list α} (i : index s) : α := s.nth_le i.index i.property

def pairable (s : list α) (t : list β) : Prop := s.length = t.length

lemma index.index_lt {s : list α} (i : index s) : i.index < s.length := i.property

lemma index.eq_of_index_eq {s : list α} {i : index s} {i' : index s} : i.index = i'.index → i = i' :=
fin.eq_of_veq

lemma index.index_eq_of_eq {s : list α} {i : index s} {i' : index s} : i = i' → i.index = i'.index :=
fin.veq_of_eq

lemma index.ne_of_index_ne {s : list α} {i : index s} {i' : index s} : i.index ≠ i'.index → i ≠ i' :=
fin.ne_of_vne

lemma index.index_ne_of_ne {s : list α} {i : index s} {i' : index s} : i ≠ i' → i.index ≠ i'.index :=
fin.vne_of_ne

@[simp] lemma index.eta {s : list α} (i : index s) (h : i.index < s.length) : (⟨i.index, h⟩ : index s) = i :=
fin.eta _ _

@[ext] lemma index.ext {s : list α} {i : index s} {i' : index s} : i.index = i'.index → i = i' :=
fin.ext

lemma index.ext_iff {s : list α} {i : index s} {i' : index s} : i = i' ↔ i.index = i'.index :=
fin.ext_iff

lemma index.index_injective {s : list α} : function.injective $ @index.index _ s :=
fin.val_injective

lemma index.eq_iff_index_eq {s : list α} (i : index s) (i' : index s) : i = i' ↔ i.index = i'.index :=
fin.eq_iff_veq _ _

lemma index.ne_iff_index_ne {s : list α} (i : index s) (i' : index s) : i ≠ i' ↔ i.index ≠ i'.index :=
fin.ne_iff_vne _ _

@[simp] lemma index.mk_eq_mk {s : list α} {i : ℕ} {h : i < s.length} {i' : ℕ} {h' : i' < s.length} :
  (⟨i, h⟩ : index s) = ⟨i', h'⟩ ↔ i = i' :=
fin.mk_eq_mk

lemma index.eq_mk_iff_index_eq {s : list α} {i : index s} {i' : ℕ} {h : i' < s.length} :
  i = ⟨i', h⟩ ↔ i.index = i' :=
fin.eq_mk_iff_coe_eq

@[simp] lemma index.index_mk {s : list α} {i : ℕ} (h : i < s.length) : index.index ⟨i, h⟩ = i :=
fin.mk_val _

lemma index.mk_index {s : list α} (i : index s) : (⟨i.index, i.property⟩ : index s) = i :=
fin.mk_coe _

lemma index.heq_ext_iff {s : list α} {t : list β} (h : pairable s t) {i : index s} {i' : index t} :
  i == i' ↔ i.index = i'.index :=
fin.heq_ext_iff h

lemma index.eq_val_of_base_eq_of_heq {s t : list α} (h : s = t) {i : index s} {i' : index t} :
  i == i' → i.val = i'.val :=
by { subst h, rw [index.heq_ext_iff rfl, ← index.eq_iff_index_eq], exact congr_arg _ }

lemma index.exists_iff {s : list α} {p : index s → Prop} :
  (∃ (i : index s), p i) ↔ ∃ (i : ℕ) (h : i < s.length), p ⟨i, h⟩ := fin.exists_iff

lemma index.forall_iff {s : list α} {p : index s → Prop} :
  (∀ (i : index s), p i) ↔ ∀ (i : ℕ) (h : i < s.length), p ⟨i, h⟩ := fin.forall_iff

lemma index.val_mem {s : list α} (i : index s) : i.val ∈ s := list.nth_le_mem _ _ _

def index.last {s : list α} (h : s ≠ []) : index s :=
⟨s.length - 1, nat.sub_lt (list.length_pos_of_ne_nil h) (nat.succ_pos 0)⟩

@[simp] lemma index.last_index {s : list α} (h : s ≠ []) : (index.last h).index = s.length - 1 := rfl

instance (s : list α) : fintype (index s) := fin.fintype _

def in_index_elim {s : list α} (f : index s → β) (g : β) (i : ℕ) : β :=
if h : i < s.length then f ⟨i, h⟩ else g

@[simp] lemma in_index_elim_yes {s : list α} (f : index s → β) (g : β) (i : index s) :
  in_index_elim f g i.index = f i :=
by simp [in_index_elim, i.index_lt]

@[simp] lemma in_index_elim_no {s : list α} (f : index s → β) (g : β) (i : ℕ)
  (h : ¬∃ (i' : index s), i'.index = i) : in_index_elim f g i = g :=
by simp [in_index_elim, λ h', h ⟨⟨i, h'⟩, rfl⟩]

lemma to_none_or_lt_id_in_index_elim_yes_none_of_forall_index {s : list α} (f : index s → option ℕ)
  (h : ∀ (i : index s), with_bot.has_lt.lt (f i) i.index) : to_none_or_lt_id (in_index_elim f none) :=
begin
  intro i,
  rw in_index_elim,
  split_ifs with h',
  { exact h ⟨i, h'⟩ },
  { exact with_bot.bot_lt_coe i }
end

lemma to_none_or_lt_id_in_index_elim_yes_none_forall_index_of {s : list α} (f : index s → option ℕ)
  (h : to_none_or_lt_id (in_index_elim f none)) : ∀ (i : index s), with_bot.has_lt.lt (f i) i.index :=
begin
  intro i,
  specialize h i.index,
  rw in_index_elim_yes at h,
  exact h
end

lemma not_map_is_some_and_lt_same {s : list α} (f : index s → option ℕ+) (i : index s) :
  i.index ∉ ((finset.image index.index $ finset.univ.filter
    (λ j : index s, option.cases_on (prod.mk <$> f j <*> f i) false (function.uncurry (<)))) : set ℕ) :=
begin
  dsimp,
  simp,
  intros j hj,
  contrapose! hj,
  rw ← index.eq_iff_index_eq at hj,
  rw hj,
  cases f i; dsimp [(<*>)],
  { exact not_false },
  { exact irrefl _ }
end

lemma pairable.def {s : list α} {t : list β} : pairable s t → s.length = t.length := id

lemma pairable.symm {s : list α} {t : list β} : pairable s t → pairable t s := symm

lemma pairable.trans {s : list α} {t : list β} {u : list γ} :
  pairable s t → pairable t u → pairable s u := eq.trans

def pairable.transfer {s : list α} {t : list β} (h : pairable s t) (i : index s) : index t :=
⟨i.index, lt_of_lt_of_eq i.property h⟩

@[simp] lemma pairable.index_transfer {s : list α} {t : list β} (h : pairable s t) (i : index s) :
  (h.transfer i).index = i.index := rfl

instance (s : list α) (t : list β) : decidable $ pairable s t := nat.decidable_eq _ _

def index₂ (m : list (list α)) : Type := Σ (i : index m), index $ index.val i

def index₂.index {m : list (list α)} (q : index₂ m) : ℕ × ℕ := (q.fst.index, q.snd.index)

def index₂.val {m : list (list α)} (q : index₂ m) : α := q.snd.val

def pairable₂ (m₁ : list (list α)) (m₂ : list (list β)) : Prop :=
∃ (h : pairable m₁ m₂), ∀ (i : index m₁), pairable i.val (h.transfer i).val

lemma index₂.fst_index_lt {m : list (list α)} (q : index₂ m) : q.fst.index < m.length :=
q.fst.index_lt

lemma index₂.snd_index_lt {m : list (list α)} (q : index₂ m) : q.snd.index < q.fst.val.length :=
q.snd.index_lt

@[simp] lemma index₂.index_fst {m : list (list α)} (q : index₂ m) : q.index.fst = q.fst.index := rfl

@[simp] lemma index₂.index_snd {m : list (list α)} (q : index₂ m) : q.index.snd = q.snd.index := rfl

lemma index₂.eq_of_index_eq {m : list (list α)} {q : index₂ m} {q' : index₂ m} (h : q.index = q'.index) : q = q' :=
have fst_eq : q.fst = q'.fst := (index.ext (index₂.index_fst q ▸ index₂.index_fst q' ▸ congr_arg _ h)),
sigma.ext fst_eq
  ((index.heq_ext_iff (congr_arg list.length (index.eq_val_of_base_eq_of_heq rfl (heq_of_eq fst_eq)))).mpr
    (index₂.index_snd q ▸ index₂.index_snd q' ▸ congr_arg _ h))

lemma index₂.index_eq_of_eq {m : list (list α)} {q : index₂ m} {q' : index₂ m} : q = q' → q.index = q'.index :=
congr_arg _

lemma index₂.ne_of_index_ne {m : list (list α)} {q : index₂ m} {q' : index₂ m} : q.index ≠ q'.index → q ≠ q' :=
mt index₂.index_eq_of_eq

lemma index₂.index_ne_of_ne {m : list (list α)} {q : index₂ m} {q' : index₂ m} : q ≠ q' → q.index ≠ q'.index :=
mt index₂.eq_of_index_eq

@[simp] lemma index₂.eta {m : list (list α)} (q : index₂ m) : (⟨q.fst, q.snd⟩ : index₂ m) = q :=
sigma.eta _

@[ext] lemma index₂.ext {m : list (list α)} {q : index₂ m} {q' : index₂ m} : q.index = q'.index → q = q' :=
index₂.eq_of_index_eq

@[simp] lemma index₂.eta₂ {m : list (list α)} (q : index₂ m)
  (h₁ : q.fst.index < m.length) (h₂ : q.snd.index < (index.val ⟨q.fst.index, h₁⟩).length) :
  (⟨⟨q.fst.index, h₁⟩, ⟨q.snd.index, h₂⟩⟩ : index₂ m) = q :=
index₂.ext rfl

@[simp] lemma index₂.eta₂' {m : list (list α)} (q : index₂ m)
  (h₁ : q.fst.index < m.length) (h₂ : q.snd.index < q.fst.val.length) :
  (⟨⟨q.fst.index, h₁⟩, ⟨q.snd.index, (index.eta q.fst h₁).symm ▸ h₂⟩⟩ : index₂ m) = q :=
index₂.eta₂ _ _ _

lemma index₂.ext_iff {m : list (list α)} {q : index₂ m} {q' : index₂ m} : q = q' ↔ q.index = q'.index :=
⟨index₂.index_eq_of_eq, index₂.eq_of_index_eq⟩

lemma index₂.index_injective {m : list (list α)} : function.injective $ @index₂.index _ m :=
@index₂.eq_of_index_eq _ _

lemma index₂.eq_iff_index_eq {m : list (list α)} (q : index₂ m) (q' : index₂ m) : q = q' ↔ q.index = q'.index :=
index₂.ext_iff

lemma index₂.ne_iff_index_ne {m : list (list α)} (q : index₂ m) (q' : index₂ m) : q ≠ q' ↔ q.index ≠ q'.index :=
iff.not index₂.ext_iff

lemma index₂.eq_iff_fst_index_eq_and_snd_index_eq {m : list (list α)} (q : index₂ m) (q' : index₂ m) :
  q = q' ↔ q.fst.index = q'.fst.index ∧ q.snd.index = q'.snd.index :=
by simp [index₂.eq_iff_index_eq, prod.eq_iff_fst_eq_snd_eq]

lemma index₂.ne_iff_fst_index_ne_or_snd_index_ne {m : list (list α)} (q : index₂ m) (q' : index₂ m) :
  q ≠ q' ↔ q.fst.index ≠ q'.fst.index ∨ q.snd.index ≠ q'.snd.index :=
by { rw [ne.def, index₂.eq_iff_fst_index_eq_and_snd_index_eq], tauto }

lemma index₂.mk_eq_mk {m : list (list α)}
  {i : index m} {j : index i.val} {i' : index m} {j' : index i'.val} :
  (⟨i, j⟩ : index₂ m) = ⟨i', j'⟩ ↔ i = i' ∧ j == j' :=
sigma.mk.inj_iff

@[simp] lemma index₂.mk_mk_eq_mk_mk {m : list (list α)}
  {i : ℕ} {hi : i < m.length} {j : ℕ} {hj : j < (index.val ⟨i, hi⟩).length}
  {i' : ℕ} {hi' : i' < m.length} {j' : ℕ} {hj' : j' < (index.val ⟨i', hi'⟩).length} :
  (⟨⟨i, hi⟩, ⟨j, hj⟩⟩ : index₂ m) = ⟨⟨i', hi'⟩, ⟨j', hj'⟩⟩ ↔ (i, j) = (i', j') :=
begin
  simp,
  intro i_eq,
  refine index.heq_ext_iff _,
  congr,
  exact i_eq
end

lemma index₂.eq_mk_mk_iff_index_eq {m : list (list α)} {q : index₂ m}
  {i' : ℕ} {hi' : i' < m.length} {j' : ℕ} {hj' : j' < (index.val ⟨i', hi'⟩).length} :
  q = ⟨⟨i', hi'⟩, ⟨j', hj'⟩⟩ ↔ q.index = (i', j') :=
by { rw index₂.ext_iff, refl }

lemma index₂.index_mk {m : list (list α)} {i : index m} {j : index i.val} :
  index₂.index ⟨i, j⟩ = (i.index, j.index) := rfl

@[simp] lemma index₂.index_mk_mk {m : list (list α)}
  {i : ℕ} {hi : i < m.length} {j : ℕ} {hj : j < (index.val ⟨i, hi⟩).length} :
  index₂.index ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ = (i, j) := rfl

lemma index₂.mk_mk_index {m : list (list α)} (q : index₂ m) : (⟨⟨q.fst.index, q.fst.property⟩, ⟨q.snd.index, q.snd.property⟩⟩ : index₂ m) = q :=
index₂.eta₂' _ _ q.snd.property

lemma index₂.exists_iff {m : list (list α)} {p : index₂ m → Prop} :
  (∃ (q : index₂ m), p q) ↔ ∃ (i : index m) (j : index i.val), p ⟨i, j⟩ := sigma.exists

lemma index₂.forall_iff {m : list (list α)} {p : index₂ m → Prop} :
  (∀ (q : index₂ m), p q) ↔ ∀ (i : index m) (j : index i.val), p ⟨i, j⟩ := sigma.forall

lemma index₂.val_mem {m : list (list α)} (q : index₂ m) : ∃ (c ∈ m), q.val ∈ c :=
⟨q.fst.val, index.val_mem _, index.val_mem _⟩

instance (m : list (list α)) : fintype (index₂ m) := sigma.fintype _

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
{s : list ℕ+ // if h : 0 < s.length then index.val (⟨0, h⟩ : index s) = 1 else true}

/-- ^𝕊 -/
def parent_list : Type :=
{t : list (option ℕ) // ∀ (i : index t), with_bot.has_lt.lt i.val i.index}

lemma parent_list.head_eq_none {t : parent_list} (h : 0 < t.val.length) :
  index.val (⟨0, h⟩ : index t.val) = none :=
(nat.with_bot.lt_zero_iff _).mp (t.property _)

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

lemma parent_mountain.is_coherent.val_eq_none_iff {P : parent_mountain} (hP : P.is_coherent) (q : index₂ P.val) :
  q.val = none ↔ q.snd.index = q.fst.val.length - 1 := (hP q).left

lemma parent_mountain.is_coherent.val_lt {P : parent_mountain} (hP : P.is_coherent) (q : index₂ P.val) :
  with_bot.has_lt.lt q.val q.fst.index := (hP q).right.left

lemma parent_mountain.is_coherent.elim_exists_index {P : parent_mountain} (hP : P.is_coherent) (q : index₂ P.val) :
  option.elim true (λ p, ∃ (q' : index₂ P.val), q'.index = (p, q.snd.index)) q.val := (hP q).right.right

instance : decidable_pred parent_mountain.is_coherent :=
λ P, fintype.decidable_forall_fintype

lemma parent_mountain.is_coherent.exists_index_of_is_some {P : parent_mountain} (hP : P.is_coherent)
  {q : index₂ P.val} (hq : q.val.is_some) :
  ∃ (q' : index₂ P.val), q'.index = (option.get hq, q.snd.index) :=
begin
  have := hP.elim_exists_index q,
  rw ← option.some_get hq at this,
  exact this
end

lemma parent_mountain.is_coherent.head_eq_none {P : parent_mountain} (hP : P.is_coherent)
  (h : 0 < P.val.length) (j : index (index.val (⟨0, h⟩ : index P.val))) :
  index₂.val (⟨⟨0, h⟩, j⟩ : index₂ P.val) = none :=
(nat.with_bot.lt_zero_iff _).mp (hP.val_lt _)

lemma parent_mountain.is_coherent.head_length {P : parent_mountain} (hP : P.is_coherent)
  (h : 0 < P.val.length) : (index.val (⟨0, h⟩ : index P.val)).length = 1 :=
begin
  have head_length_pos := list.length_pos_of_ne_nil (P.property _ (index.val_mem ⟨0, h⟩)),
  rw ← nat.sub_eq_iff_eq_add head_length_pos,
  exact ((hP.val_eq_none_iff ⟨⟨0, h⟩, ⟨0, head_length_pos⟩⟩).mp (hP.head_eq_none _ _)).symm
end

def parent_mountain.is_coherent.index_parent_of_is_some {P : parent_mountain} (hP : P.is_coherent)
  {q : index₂ P.val} (hq : q.val.is_some) :
  {q' : index₂ P.val // let i := q.fst.index, j := q.snd.index in q'.index = (option.get hq, j)} :=
⟨⟨⟨option.get hq, begin
  cases hP.exists_index_of_is_some hq with q' hq',
  rw index₂.index at hq',
  simp at hq',
  exact lt_of_eq_of_lt hq'.left.symm q'.fst_index_lt
end⟩,
  ⟨q.snd.index, begin
  cases hP.exists_index_of_is_some hq with q' hq',
  rw index₂.index at hq',
  simp at hq',
  refine lt_of_eq_of_lt hq'.right.symm (lt_of_lt_of_eq q'.snd_index_lt _),
  congr,
  exact index.eq_of_index_eq hq'.left
end⟩⟩, rfl⟩

def parent_mountain.is_coherent.index_above_of_is_some {P : parent_mountain} (hP : P.is_coherent)
  {q : index₂ P.val} (hq : q.val.is_some) :
  {q' : index₂ P.val // let i := q.fst.index, j := q.snd.index in q'.index = (i, j + 1)} :=
⟨⟨q.fst, ⟨q.snd.index + 1, begin
  have h := (not_iff_not.mpr (hP.val_eq_none_iff q)).mp (option.ne_none_iff_is_some.mpr hq),
  rw lt_iff_le_and_ne,
  split,
  { exact nat.succ_le_of_lt q.snd_index_lt },
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
  1 < (index₂.val (⟨i, ⟨0,
    list.length_pos_of_ne_nil (x.values.property _ (index.val_mem _))⟩⟩ : index₂ x.values.val)).val → 
  (index₂.val (⟨x.pairable.fst.transfer i, ⟨0,
    list.length_pos_of_ne_nil (x.parents.property _ (index.val_mem _))⟩⟩ : index₂ x.parents.val)).is_some

lemma mountain.head_value_eq_one_of_parents_is_coherent_of_is_orphanless_of_length_pos {x : mountain}
  (h_coherent : x.parents.is_coherent) (h_orphanless : x.is_orphanless)
  (len_pos : 0 < x.values.val.length) :
  index₂.val (⟨⟨0, len_pos⟩, ⟨0,
    list.length_pos_of_ne_nil (x.values.property _ (index.val_mem _))⟩⟩ : index₂ x.values.val) = 1 :=
begin
  by_contra H,
  have := h_orphanless ⟨0, len_pos⟩
    begin
      apply lt_of_le_of_ne (pnat.one_le _) (ne.symm H),
    end,
  rw ← option.ne_none_iff_is_some at this,
  exact absurd (h_coherent.head_eq_none (lt_of_lt_of_eq len_pos x.pairable.fst) _) this,
end

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
          ⟨index.index, index.index_injective⟩)
      (by apply_instance) i.index in
have to_none_or_lt_id_parent : to_none_or_lt_id (in_index_elim parent none) :=
  begin
    apply to_none_or_lt_id_in_index_elim_yes_none_of_forall_index,
    intro i,
    apply to_none_or_lt_id_find_iterate_of_not_mem,
    simp,
    intro k,
    contrapose!,
    intro hk,
    rw index.eq_of_index_eq hk,
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
    rcases @parent_as_index i h with ⟨⟨p, hp₁⟩, hp₂⟩,
    simp [hk, index.index] at hp₂,
    subst hp₂,
    have spec : option.elim true _ (parent i) := find_iterate_spec _ _ _,
    rw [hk, option.elim, ← @set.mem_def _ _ (coe _)] at spec,
    simp at spec,
    rcases spec with ⟨⟨p', hp'₁⟩, hp'₂, hp'₃⟩,
    simp [hk, index.index] at hp'₃,
    symmetry' at hp'₃,
    subst hp'₃,
    exact hp'₂
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
    apply to_none_or_lt_id_in_index_elim_yes_none_of_forall_index,
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
  generalize_proofs hvp₀ hvt₀,
  obtain ⟨m, hm⟩ := option.is_some_iff_exists.mp hvp₀,
  obtain ⟨n, hn⟩ := option.is_some_iff_exists.mp hvt₀,
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
      apply to_none_or_lt_id_in_index_elim_yes_none_of_forall_index,
      intro,
      rw ← pairable.index_transfer x.pairable _,
      exact x.parents.property _
    end
    ((finset.univ.filter (λ (p : index x.values.val),
      option.cases_on (prod.mk <$> value x p 0 <*> value x i 0) false (function.uncurry (<)))).map
        ⟨index.index, index.index_injective⟩)
    (by apply_instance) i.index := rfl

@[simp] lemma parent_succ (x : value_parent_list_pair) (i : index x.values.val) (j : ℕ) :
  parent x i (j + 1) = @find_iterate_of_to_none_or_lt_id
    (in_index_elim (λ p, parent x p j) none)
    (to_none_or_lt_id_parent x j)
    ((finset.univ.filter (λ (p : index x.values.val),
      option.cases_on (prod.mk <$> value x p (j + 1) <*> value x i (j + 1)) false (function.uncurry (<)))).map
        ⟨index.index, index.index_injective⟩)
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
  generalize_proofs hva₀ hvt₀ hvp₀,
  obtain ⟨⟨vt, vt_pos⟩, hvt⟩ := option.is_some_iff_exists.mp hvt₀,
  obtain ⟨⟨vp, vp_pos⟩, hvp⟩ := option.is_some_iff_exists.mp hvp₀,
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
  generalize_proofs hvt₀ hvp₀,
  obtain ⟨⟨vt, vt_pos⟩, hvt⟩ := option.is_some_iff_exists.mp hvt₀,
  obtain ⟨⟨vp, vp_pos⟩, hvp⟩ := option.is_some_iff_exists.mp hvp₀,
  simp [hvt, hvp, value_succ, -subtype.val_eq_coe],
  exact nat.sub_lt vt_pos vp_pos
end

lemma pnat.sub_val_eq_iff_eq_add {a b c : ℕ+} /- (ab : b < a) -/ : a.val - b.val = c.val ↔ a = c + b :=
begin
  cases a with a a_pos,
  cases b with b b_pos,
  cases c with c c_pos,
  obtain ⟨c, rfl⟩ := nat.exists_eq_succ_of_ne_zero (ne_of_gt c_pos),
  dsimp,
  split; intro h,
  { have h' := congr_arg (+ b) h,
    simp only [] at h',
    apply pnat.eq,
    dsimp,
    convert ← h',
    exact nat.sub_add_cancel (nat.le_of_lt (nat.lt_of_sub_eq_succ h)) },
  { have h' := congr_arg subtype.val h,
    dsimp at h',
    exact tsub_eq_of_eq_add h' }
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
  { have va_lt_vt := value_above_lt_value_of_parent_is_some h,
    generalize_proofs hva₀ hvp₀ at va_lt_vt,
    obtain ⟨⟨vt, vt_pos⟩, hvt⟩ := option.is_some_iff_exists.mp hvp₀,
    obtain ⟨⟨va, va_pos⟩, hva⟩ := option.is_some_iff_exists.mp hva₀,
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

lemma value_eq_none_of_height_le {x : value_parent_list_pair} {i : index x.values.val} {j : ℕ}
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
    exact option.is_none_iff_eq_none.mpr (value_eq_none_of_height_le H)
  end,
  value_is_some_of_lt_height⟩

lemma value_eq_none_iff_height_le {x : value_parent_list_pair} {i : index x.values.val} {j : ℕ} :
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
      exact q.snd_index_lt,
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
      value_eq_none_iff_height_le],
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
    exact absurd j.index_lt (not_lt_of_le h) },
  { refine lt_of_eq_of_lt _ (to_none_or_lt_id_parent x j.index i.index),
    symmetry,
    simp only [in_index_elim],
    rw [dite_eq_iff', and_iff_left],
    swap,
    { intro h,
      refine absurd (lt_of_lt_of_eq i.index_lt _) h,
      exact (build_mountain x).pairable.fst.symm.trans (mountain_length_eq x) },
    intro,
    rw mountain_parent_at_index_eq_parent,
    refl },
  { cases h : index₂.val _ with k,
    { triv },
    { rw mountain_parent_at_index_eq_parent at h,
      have parent_is_some := option.is_some_iff_exists.mpr ⟨k, h⟩,
      let q := (parent_as_index parent_is_some),
      let p := q.val,
      refine ⟨⟨pairable.transfer
            ((mountain_length_eq x).symm.trans (build_mountain x).pairable.fst) p,
          ⟨j.index, _⟩⟩, _⟩,
      { apply eq.subst ((mountain_height_eq' x _).symm.trans ((build_mountain x).pairable.snd _)),
        rw ← value_is_some_iff_lt_height,
        exact value_parent_is_some_of_parent_is_some parent_is_some },
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
      ∃ (k : ℕ) (h : option.is_some _) (p : index _), _ < i₀_on_lv.val ∧ _)
    i₀ _ hi₀ value₀_gt_one,
  intros i IH hi value_gt_one i_has_parent_candidate,
  let i_on_mv : index _ := ⟨i, hi⟩,
  let i_on_lv : index _ := pairable.transfer (mountain_length_eq x) i_on_mv,
  let i_on_lp : index _ := pairable.transfer ((mountain_length_eq x).trans x.pairable) i_on_mv,
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
    congr },
  all_goals
  { have := i_on_lv.index_lt,
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
  simp only [mountain_value_at_index_eq_value, mountain_parent_at_index_eq_parent, pairable.transfer, index.index, option.get_some],
  generalize_proofs hi' hva₀ hvt₀ hp₀ hj' hvp₀,
  simp [mountain_parent_at_index_eq_parent, pairable.transfer, index.index] at hq,
  obtain ⟨⟨vt, vt_pos⟩, hvt⟩ := option.is_some_iff_exists.mp hvt₀,
  obtain ⟨⟨vp, vp_pos⟩, hvp⟩ := option.is_some_iff_exists.mp hvp₀,
  obtain ⟨⟨va, va_pos⟩, hva⟩ := option.is_some_iff_exists.mp hva₀,
  simp only [hvt, hvp, hva, option.get_some],
  clear hi' hj' hvt₀ hvp₀ hva₀,
  rcases hp : parent_as_index hq with ⟨⟨p, hp₁⟩, hp₂⟩,
  simp only [← hp₂, index.index] at hvp,
  have vp_lt_vt := value_parent_lt_value hq,
  simp [hvt, hp, hvp, option.get_some] at vp_lt_vt,
  have va_eq := val_value_above_eq_of_parent_is_some hq,
  simp [hvt, hp, hvp, hva, -subtype.val_eq_coe] at va_eq,
  simp [va_eq, ← pnat.coe_inj, pnat.sub_coe, vp_lt_vt]
end

theorem build_mountain_orphanless_is_coherent (x : value_parent_list_pair) (h : x.is_orphanless) :
  (build_mountain x).is_coherent :=
⟨build_mountain_orphanless_is_orphanless x h, build_mountain_orphanless_is_cross_coherent x h⟩

end build


section diagonal

def surface_at {V : value_mountain} (i : index V.val) : ℕ+ :=
index₂.val ⟨i, index.last (V.property _ (index.val_mem i))⟩

def descend {P : parent_mountain} (hP : P.is_coherent) (q : index₂ P.val) : option (index₂ P.val) :=
if h : q.val.is_some
then some (hP.index_parent_of_is_some h)
else match q.snd with
| ⟨0    , _⟩ := none
| ⟨j + 1, h⟩ := some ⟨q.fst, ⟨j, lt_trans (nat.lt_succ_self j) h⟩⟩
end

def descend_eq_none_iff {P : parent_mountain} (hP : P.is_coherent) (q : index₂ P.val) :
  descend hP q = none ↔ ¬q.val.is_some ∧ q.snd.index = 0 :=
begin
  rw descend,
  split_ifs with h,
  { simp [h] },
  { rcases q.snd with ⟨_ | j, hj⟩; simp [descend, h] }
end

def descend_eq_none_iff' {P : parent_mountain} (hP : P.is_coherent) (q : index₂ P.val) :
  descend hP q = none ↔ q.val = none ∧ q.snd.index = 0 :=
by { rw ← @option.not_is_some_iff_eq_none _ q.val, exact descend_eq_none_iff hP q }

def descend_is_some_iff {P : parent_mountain} (hP : P.is_coherent) (q : index₂ P.val) :
  (descend hP q).is_some ↔ q.val.is_some ∨ q.snd.index ≠ 0 :=
begin
  rw descend,
  split_ifs with h,
  { simp [h] },
  { rcases q.snd with ⟨_ | j, hj⟩; simp [descend, h] }
end

theorem descend_lt_and_eq_or_eq_and_lt_of_it_is_some {P : parent_mountain} {hP : P.is_coherent}
  {q : index₂ P.val} (h : (descend hP q).is_some) :
  let i := q.fst.index, j := q.snd.index,
    q' := option.get h, i' := q'.fst.index, j' := q'.snd.index in
  i' < i ∧ j' = j ∨ i' = i ∧ j' < j :=
begin
  intros i j q' i' j',
  have q'_eq := eq.refl q',
  conv_rhs at q'_eq { simp only [q'] },
  simp only [descend] at q'_eq,
  split_ifs at q'_eq with hq_val,
  { left,
    simp only [option.get_some] at q'_eq,
    obtain ⟨k, hk⟩ := option.is_some_iff_exists.mp hq_val,
    obtain ⟨p, hp⟩ := hP.index_parent_of_is_some hq_val,
    intro q'_eq,
    simp only [subtype.coe_mk] at q'_eq,
    subst q'_eq,
    simp [hk, option.get_some, prod.eq_iff_fst_eq_snd_eq] at hp,
    cases hp with hp₁ hp₂,
    have q_val_lt := (hP q).right.left,
    rw [hk, ← hp₁, with_bot.some_eq_coe, with_bot.coe_lt_coe] at q_val_lt,
    exact ⟨q_val_lt, hp₂⟩ },
  { rcases q_eq : q with ⟨⟨i₁, hi⟩, ⟨j₁, hj⟩⟩,
    have : i = i₁ := congr_arg (λ (q : index₂ P.val), q.fst.index) q_eq,
    subst this,
    have : j = j₁ := congr_arg (λ (q : index₂ P.val), q.snd.index) q_eq,
    subst this,
    conv_rhs at q'_eq { congr, rw q_eq },
    cases hk : j with k,
    { generalize_proofs H at q'_eq,
      simp [hk, descend, option.get] at H,
      contradiction },
    { right,
      simp [hk] at q'_eq,
      replace q'_eq := congr_arg index₂.index q'_eq,
      simp [index₂.index, index.index] at q'_eq,
      exact ⟨q'_eq.left, lt_of_eq_of_lt q'_eq.right (lt_add_one k)⟩ } }
end

lemma descend_pairwise_le_of_it_is_some {P : parent_mountain} {hP : P.is_coherent}
  {q : index₂ P.val} (h : (descend hP q).is_some) :
  let i := q.fst.index, j := q.snd.index,
    q' := option.get h, i' := q'.fst.index, j' := q'.snd.index in i' ≤ i ∧ j' ≤ j :=
begin
  rcases descend_lt_and_eq_or_eq_and_lt_of_it_is_some h with ⟨h'₁, h'₂⟩ | ⟨h'₁, h'₂⟩,
  { exact ⟨le_of_lt h'₁, le_of_eq h'₂⟩ },
  { exact ⟨le_of_eq h'₁, le_of_lt h'₂⟩ }
end

lemma descend_pairwise_ne_of_it_is_some {P : parent_mountain} {hP : P.is_coherent}
  {q : index₂ P.val} (h : (descend hP q).is_some) : q ≠ option.get h :=
begin
  intro H,
  rcases descend_lt_and_eq_or_eq_and_lt_of_it_is_some h with ⟨h'₁, h'₂⟩ | ⟨h'₁, h'₂⟩,
  { exact absurd (congr_arg (λ (q : index₂ P.val), q.fst.index) H.symm) (ne_of_lt h'₁) },
  { exact absurd (congr_arg (λ (q : index₂ P.val), q.snd.index) H.symm) (ne_of_lt h'₂) }
end

theorem iterate_descend_pairwise_le_of_it_is_some {P : parent_mountain} {hP : P.is_coherent}
  {q : index₂ P.val} {k : ℕ} (h : ((flip bind (descend hP))^[k] $ some q).is_some) :
  let i := q.fst.index, j := q.snd.index,
    q' := option.get h, i' := q'.fst.index, j' := q'.snd.index in i' ≤ i ∧ j' ≤ j :=
begin
  induction k with k IH,
  { split; refl },
  { simp_rw ← index₂.index_snd,
    simp only [function.iterate_succ_apply'] at h ⊢,
    suffices,
    { specialize IH this,
      obtain ⟨q', hq'⟩ := option.is_some_iff_exists.mp this,
      simp_rw ← index₂.index_snd at IH,
      simp [hq'] at IH h ⊢,
      have h' := descend_pairwise_le_of_it_is_some h,
      exact ⟨le_trans h'.left IH.left, le_trans h'.right IH.right⟩ },
    by_contra H,
    rw option.not_is_some_iff_eq_none at H,
    rw H at h,
    contradiction }
end

theorem iterate_descend_succ_ne_of_it_is_some {P : parent_mountain} {hP : P.is_coherent}
  {q : index₂ P.val} {k : ℕ} (h : ((flip bind (descend hP))^[k + 1] $ some q).is_some) :
  q ≠ option.get h :=
begin
  have h' : (descend hP q).is_some,
  { induction k with k IH,
    { exact h },
    { apply IH,
      by_contra H,
      rw option.not_is_some_iff_eq_none at H,
      rw [function.iterate_succ_apply', H] at h,
      contradiction } },
  obtain ⟨q', hq'⟩ := option.is_some_iff_exists.mp h',
  have eq_iterate_from := function.iterate_succ_apply (flip bind (descend hP)) k (some q),
  change flip bind (descend hP) (some q) with descend hP q at eq_iterate_from,
  rw hq' at eq_iterate_from,
  rw eq_iterate_from at h,
  simp only [eq_iterate_from],
  have hq'₂ := eq.refl (option.get h'),
  conv_rhs at hq'₂ { simp only [hq', option.get_some] },
  have h₁ := descend_lt_and_eq_or_eq_and_lt_of_it_is_some h',
  rw hq'₂ at h₁,
  have h₂ := iterate_descend_pairwise_le_of_it_is_some h,
  rw [ne, index₂.eq_iff_index_eq, prod.eq_iff_fst_eq_snd_eq, decidable.not_and_distrib],
  simp,
  cases h₁,
  { exact or.inl (ne_of_lt (lt_of_le_of_lt h₂.left h₁.left)).symm },
  { exact or.inr (ne_of_lt (lt_of_le_of_lt h₂.right h₁.right)).symm }
end

theorem descend_finite {P : parent_mountain} (hP : P.is_coherent) : iterate_eventually_none $ descend hP :=
begin
  refine λ q, @is_well_founded.induction (option (index₂ P.val))
    (with_bot.has_lt.lt on option.map (λ q, q.fst.index + q.snd.index))
    ⟨inv_image.wf _ (is_well_order.to_is_well_founded.wf : well_founded _)⟩ _ q _,
  clear q,
  intros q IH,
  cases q with q,
  { exact ⟨0, rfl⟩ },
  { choose! k hk using IH,
    cases h : descend hP q with q',
    { exact ⟨1, h⟩ },
    { refine ⟨k (descend hP q) + 1, hk _ _⟩,
      simp [h, function.on_fun],
      have h' := descend_lt_and_eq_or_eq_and_lt_of_it_is_some (option.is_some_iff_exists.mpr ⟨_, h⟩),
      simp_rw ← index₂.index_snd at h',
      simp [h] at h',
      rcases h' with ⟨h'₁, h'₂⟩ | ⟨h'₁, h'₂⟩,
      { simp only [add_lt_add_iff_right, h'₁, h'₂] },
      { simp only [add_lt_add_iff_left, h'₁, h'₂] } } }
end

def descend_to_surface {P : parent_mountain} (hP : P.is_coherent) (q : index₂ P.val) : option (index P.val) :=
sigma.fst <$> @find_iterate_of_iterate_eventually_none _
  (descend hP) (descend_finite hP)
  (finset.univ.filter (λ (p : index₂ P.val), p.val = none ∧ p.fst ≠ q.fst))
  (by apply_instance) q

lemma exists_iterate_descend_spec_of_descend_to_surface_is_some {P : parent_mountain} (hP : P.is_coherent)
  (q : index₂ P.val) (h : (descend_to_surface hP q).is_some) :
  ∃ (k : ℕ) (hk : ((flip bind (descend hP))^[k] $ some q).is_some),
    (option.get hk).fst = option.get h ∧ (option.get hk).val = none ∧ (option.get hk).fst ≠ q.fst :=
begin
  obtain ⟨i', hi'⟩ := option.is_some_iff_exists.mp h,
  have hi'₂ := hi',
  simp only [descend_to_surface] at hi'₂,
  simp at hi'₂,
  cases hi'₂ with j' hi'j',
  refine ⟨_, option.is_some_iff_exists.mpr ⟨_, hi'j'⟩, ⟨_, _⟩⟩,
  { conv_lhs
    begin
      congr,
      congr,
      change find_iterate_of_iterate_eventually_none _ _ q,
    end,
    simp [hi'j', hi'] },
  { have : option.elim true _ _ := @eq.subst _ _ _ _ hi'j' (find_iterate_spec _ _ _),
    rw [option.elim, ← @set.mem_def _ _ (coe _)] at this,
    simp at this,
    convert this,
    { rw [← option.some.inj_eq, option.some_get],
      exact hi'j' },
    { conv_lhs
      begin
        congr,
        congr,
        change find_iterate_of_iterate_eventually_none _ _ q,
      end,
      simp [hi'j'] } }
end

lemma descend_to_surface_to_none_or_lt_fst_index {P : parent_mountain} (hP : P.is_coherent) (q : index₂ P.val) :
  with_bot.has_lt.lt ((descend_to_surface hP q).map index.index) q.fst.index :=
begin
  cases h : descend_to_surface hP q,
  { exact with_bot.none_lt_some _ },
  { have h' := option.is_some_iff_exists.mpr ⟨_, h⟩,
    obtain ⟨k, hk₁, hk₂⟩ := exists_iterate_descend_spec_of_descend_to_surface_is_some hP q h',
    simp only [h, option.get_some] at hk₂,
    rw [option.map_some', with_bot.some_eq_coe, with_bot.coe_lt_coe, ← hk₂.left],
    have h'' := iterate_descend_pairwise_le_of_it_is_some hk₁,
    exact lt_of_le_of_ne h''.left (index.index_ne_of_ne hk₂.right.right) }
end

theorem descend_to_surface_is_some_iff {P : parent_mountain} (hP : P.is_coherent) (q : index₂ P.val) :
  (descend_to_surface hP q).is_some ↔ 0 < q.snd.index ∨ q.val.is_some :=
begin
  rw [descend_to_surface, option.is_some_iff_exists],
  generalize_proofs descend_finite,
  generalize mem_decidable_def : (λ _, finset.decidable_mem' _ _) = mem_decidable,
  simp,
  transitivity ∃ (q' : index₂ P.val), find_iterate_of_iterate_eventually_none descend_finite mem_decidable q = some q',
  { convert sigma.exists.symm,
    funext,
    congr },
  subst mem_decidable_def,
  rw [← option.is_some_iff_exists, find_iterate_is_some_iff],
  split,
  { rintro ⟨k, hk₁, hk₂⟩,
    have k_ne_zero : k ≠ 0,
    { intro H,
      subst H,
      simp at hk₂,
      simp [set.mem_def] at hk₂,
      exact hk₂ },
    obtain ⟨k, rfl⟩ := nat.exists_eq_succ_of_ne_zero k_ne_zero,
    clear k_ne_zero hk₂,
    by_contra H,
    rcases q with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩,
    rw decidable.not_or_iff_and_not at H,
    cases H with H' H,
    simp [index.index] at H',
    subst H',
    induction k with k IH,
    { simp [flip, descend, H] at hk₁, exact hk₁ },
    { rw [imp_false, option.not_is_some_iff_eq_none] at IH,
      rw [function.iterate_succ_apply', IH] at hk₁,
      contradiction } },
  { have descend_finite_on_q := descend_finite (some q),
    generalize k_def : nat.find descend_finite_on_q = k,
    obtain ⟨hk_eq, hk_lt⟩ := (nat.find_eq_iff descend_finite_on_q).mp k_def,
    have k_ne_zero : k ≠ 0,
    { intro H,
      subst H,
      contradiction },
    obtain ⟨k, rfl⟩ := nat.exists_eq_succ_of_ne_zero k_ne_zero,
    clear k_ne_zero,
    intro h,
    have last_is_some := option.ne_none_iff_is_some.mp (hk_lt k (lt_add_one k)),
    refine ⟨k, last_is_some, _⟩,
    simp,
    rw set.mem_def,
    have last_pairwise_le := iterate_descend_pairwise_le_of_it_is_some last_is_some,
    dsimp at last_pairwise_le,
    generalize hr : option.get last_is_some = r,
    rw hr at last_pairwise_le,
    have hr' := congr_arg option.some hr,
    rw option.some_get at hr',
    rw [function.iterate_succ_apply', hr'] at hk_eq,
    simp [flip, descend_eq_none_iff'] at hk_eq,
    split,
    { exact hk_eq.left },
    { conv at last_pairwise_le
      begin
        rw [le_iff_lt_or_eq, or_and_distrib_right],
        congr,
        skip,
        rw [le_iff_lt_or_eq, and_or_distrib_left]
      end,
      rcases last_pairwise_le with _ | _ | _,
      { exact index.ne_of_index_ne (ne_of_lt last_pairwise_le.left) },
      { refine absurd hk_eq.left ((not_iff_not_of_iff (hP.val_eq_none_iff r)).mpr (ne_of_lt _)),
        rw [← nat.pred_eq_sub_one, nat.lt_pred_iff],
        refine lt_of_lt_of_le (nat.succ_lt_succ last_pairwise_le.right) (nat.succ_le_of_lt _),
        rw index.eq_of_index_eq last_pairwise_le.left,
        exact q.snd_index_lt },
      { rw ← index₂.eq_iff_fst_index_eq_and_snd_index_eq at last_pairwise_le,
        subst last_pairwise_le,
        cases h,
        { exact absurd hk_eq.right (ne_of_lt h).symm },
        { exact absurd hk_eq.left (option.ne_none_iff_is_some.mpr h) } } } }
end

def diagonal_preparent_of {P : parent_mountain} (hP : P.is_coherent) (i : index P.val) : option (index P.val) :=
descend_to_surface hP ⟨i, index.last (P.property _ (index.val_mem i))⟩

theorem diagonal_preparent_of_is_some_iff {P : parent_mountain} (hP : P.is_coherent) (i : index P.val) :
  (diagonal_preparent_of hP i).is_some ↔ 1 < i.val.length :=
begin
  simp [diagonal_preparent_of, descend_to_surface_is_some_iff],
  intro h,
  exfalso,
  rw ← option.ne_none_iff_is_some at h,
  apply h,
  simp [hP.val_eq_none_iff]
end

theorem to_none_or_lt_diagonal_preparent {P : parent_mountain} (hP : P.is_coherent) :
  to_none_or_lt_id $ in_index_elim (option.map index.index ∘ diagonal_preparent_of hP) none :=
begin
  apply to_none_or_lt_id_in_index_elim_yes_none_of_forall_index,
  intro q,
  exact descend_to_surface_to_none_or_lt_fst_index hP _
end

def diagonal {x : mountain} (h_coherent : x.parents.is_coherent) (h_orphanless : x.is_orphanless) :
  value_parent_list_pair :=
{ values := ⟨surface_at <$> list.fin_range x.values.val.length,
    begin
      simp,
      split_ifs,
      { rw index.val,
        simp [surface_at, index.last],
        have := eq.trans (x.pairable.snd ⟨0, h⟩) (h_coherent.head_length _),
        generalize_proofs,
        simp [this],
        exact mountain.head_value_eq_one_of_parents_is_coherent_of_is_orphanless_of_length_pos
          h_coherent h_orphanless h },
      { triv }
    end⟩,
  parents := ⟨(option.map index.index ∘ diagonal_preparent_of h_coherent) <$>
      list.fin_range x.parents.val.length,
    begin
      have := to_none_or_lt_id_in_index_elim_yes_none_forall_index_of _
        (to_none_or_lt_diagonal_preparent h_coherent),
      rintro ⟨i, hi⟩,
      simp [index.val],
      exact this _
    end⟩,
  pairable := by { simp [pairable], exact x.pairable.fst } }

lemma diagonal_length_eq {x : mountain} (h_coherent : x.parents.is_coherent) (h_orphanless : x.is_orphanless) :
  (diagonal h_coherent h_orphanless).values.val.length = x.values.val.length := by simp [diagonal]

@[simp] lemma diagonal_value_at {x : mountain} (h_coherent : x.parents.is_coherent)
  (h_orphanless : x.is_orphanless) (i : index (diagonal h_coherent h_orphanless).values.val) :
  i.val = surface_at (pairable.transfer (diagonal_length_eq h_coherent h_orphanless) i) :=
by simp [pairable.transfer, index.val, diagonal]

@[simp] lemma diagonal_parent_at {x : mountain} (h_coherent : x.parents.is_coherent)
  (h_orphanless : x.is_orphanless) (i : index (diagonal h_coherent h_orphanless).parents.val) :
  i.val = index.index <$> diagonal_preparent_of h_coherent
    (pairable.transfer
      (((diagonal h_coherent h_orphanless).pairable.symm.trans
        (diagonal_length_eq h_coherent h_orphanless)).trans
        x.pairable.fst)
      i) :=
by simp [pairable.transfer, index.val, diagonal]

theorem diagonal_is_orphanless {x : mountain} (h_coherent : x.parents.is_coherent)
  (h_orphanless : x.is_orphanless) : (diagonal h_coherent h_orphanless).is_orphanless :=
begin
  intro i,
  simp [pairable.transfer],
  intro h,
  rw option.is_some_iff_exists,
  simp,
  rw exists_comm,
  simp [exists_and_distrib_left],
  rw [← option.is_some_iff_exists, diagonal_preparent_of_is_some_iff, nat.one_lt_iff_ne_zero_and_ne_one],
  split,
  { exact (ne_of_lt (list.length_pos_of_ne_nil (x.parents.property _ (index.val_mem _)))).symm },
  { intro H,
    rw [surface_at, index.last] at h,
    simp [(x.pairable.snd _).def, pairable.transfer, H] at h,
    replace h := h_orphanless _ h,
    rw [← option.ne_none_iff_is_some, ne.def, h_coherent.val_eq_none_iff] at h,
    simp [pairable.transfer, H] at h,
    exact h }
end

end diagonal

end ysequence