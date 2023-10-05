import busybeaver.defs

namespace BB

section
variables {Γ Λ : Type*} [inhabited Γ] [inhabited Λ]

@[simp] lemma multistep'_zero {M : machine Γ Λ} {c} : multistep' M 0 c = c := rfl

lemma multistep'_succ {M : machine Γ Λ} {n c} : multistep' M (n + 1) c = multistep' M n (step' M c) := rfl

lemma multistep'_succ' {M : machine Γ Λ} {n c} : multistep' M (n + 1) c = step' M (multistep' M n c) :=
function.iterate_succ_apply' (step' M) n c

@[simp] lemma multistep_zero {M : machine Γ Λ} {c} : multistep M 0 c = c := rfl

lemma multistep_succ {M : machine Γ Λ} {n c} : multistep M (n + 1) c = multistep' M n (step M c) := rfl

lemma multistep_succ' {M : machine Γ Λ} {n c} : multistep M (n + 1) c = step' M (multistep M n c) :=
function.iterate_succ_apply' (step' M) n c

lemma is_some_of_is_some_step' {M : machine Γ Λ} {c} : (step' M c).is_some → c.is_some :=
begin
  repeat {rw option.is_some_iff_exists},
  simp [step'],
  tauto,
end

lemma is_some_of_is_some_multistep' {M : machine Γ Λ} {n c} : (multistep' M n c).is_some → c.is_some :=
begin
  induction n with n IH generalizing c,
  { tauto },
  { intro h,
    exact is_some_of_is_some_step' (IH h) }
end

@[simp, refl] theorem correct_multistep_zero_iff_refl {M : machine Γ Λ} (c₀ c₁) : c₀[M]▸^[0]c₁ ↔ c₀ = c₁ :=
begin
  split,
  { intro h,
    simp [correct_multistep] at h,
    exact option.some_inj.mp h },
  { exact congr_arg _ }
end

@[simp] lemma correct_multistep_one_iff_correct_step {M : machine Γ Λ} (c₀ c₁) : c₀[M]▸^[1]c₁ ↔ c₀[M]▸c₁ :=
⟨rfl.mp, congr_arg _⟩

lemma exists_correct_step_iff_not_halted {M : machine Γ Λ} (c₀) : (∃ c₁, c₀[M]▸c₁) ↔ ¬halted c₀ :=
by split; rcases c₀ with ⟨_|q, _⟩; tauto

theorem correct_multistep_succ_iff {M : machine Γ Λ} (n c₀ c₁) : c₀[M]▸^[n + 1]c₁ ↔ ∃ c₂, c₀[M]▸c₂ ∧ c₂[M]▸^[n]c₁ :=
begin
  simp [correct_multistep, multistep_succ],
  split,
  { intro h,
    obtain ⟨c₂, hc₂⟩ := option.is_some_iff_exists.mp (is_some_of_is_some_multistep' (option.is_some_iff_exists.mpr ⟨_, h⟩)),
    use c₂,
    split,
    { exact hc₂ },
    { rw hc₂ at h,
      exact h } },
  { intro h,
    rcases h with ⟨c₂, ⟨h₁, h₂⟩⟩,
    simp [correct_step] at h₁,
    rw h₁,
    exact h₂ }
end

theorem correct_multistep_add_iff {M : machine Γ Λ} (m n c₀ c₁) : c₀[M]▸^[m + n]c₁ ↔ ∃ c₂, c₀[M]▸^[m]c₂ ∧ c₂[M]▸^[n]c₁ :=
begin
  induction m with m IH generalizing c₀,
  { simp },
  { have : (m + 1) + n = (m + n) + 1 := by finish,
    rw this,
    split,
    { intro h,
      obtain ⟨c₂, hc₂⟩ := (correct_multistep_succ_iff _ _ _).mp h,
      obtain ⟨c₃, hc₃⟩ := (IH _).mp hc₂.right,
      exact ⟨c₃, ⟨(correct_multistep_succ_iff _ _ _).mpr ⟨_, ⟨hc₂.left, hc₃.left⟩⟩, hc₃.right⟩⟩ },
    { intro h,
      cases h with c₂ hc₂,
      obtain ⟨c₃, hc₃⟩ := (correct_multistep_succ_iff _ _ _).mp hc₂.left,
      rw correct_multistep_succ_iff,
      exact ⟨c₃, ⟨hc₃.left, (IH _).mpr ⟨c₂, ⟨hc₃.right, hc₂.right⟩⟩⟩⟩ } }
end

theorem correct_multistep_succ_iff' {M : machine Γ Λ} (n c₀ c₁) : c₀[M]▸^[n + 1]c₁ ↔ ∃ c₂, c₀[M]▸^[n]c₂ ∧ c₂[M]▸c₁ :=
by simp [correct_multistep_add_iff]

@[trans] theorem correct_step_correst_step_trans_correct_multistep {M : machine Γ Λ} (c₀ c₁ c₂) : c₀[M]▸c₁ → c₁[M]▸c₂ → c₀[M]▸^[2]c₂ :=
λ h₁ h₂, (correct_multistep_succ_iff _ _ _).mpr ⟨c₁, ⟨h₁, h₂⟩⟩

@[trans] theorem correct_multistep_correst_step_trans {M : machine Γ Λ} (n c₀ c₁ c₂) : c₀[M]▸^[n]c₁ → c₁[M]▸c₂ → c₀[M]▸^[n + 1]c₂ :=
λ h₁ h₂, (correct_multistep_succ_iff' _ _ _).mpr ⟨c₁, ⟨h₁, h₂⟩⟩

@[trans] theorem correct_step_correst_multistep_trans {M : machine Γ Λ} (n c₀ c₁ c₂) : c₀[M]▸c₁ → c₁[M]▸^[n]c₂ → c₀[M]▸^[n + 1]c₂ :=
λ h₁ h₂, (correct_multistep_succ_iff _ _ _).mpr ⟨c₁, ⟨h₁, h₂⟩⟩

@[trans] theorem correst_multistep_trans {M : machine Γ Λ} (m n c₀ c₁ c₂) : c₀[M]▸^[m]c₁ → c₁[M]▸^[n]c₂ → c₀[M]▸^[m + n]c₂ :=
λ h₁ h₂, (correct_multistep_add_iff _ _ _ _).mpr ⟨c₁, ⟨h₁, h₂⟩⟩

theorem exists_correct_multistep_le_of_correct_multistep {M : machine Γ Λ} (n c₀ c₁) : c₀[M]▸^[n]c₁ → ∀ m ≤ n, ∃ c₂, c₀[M]▸^[m]c₂ :=
begin
  induction n with n IH generalizing c₁,
  { intros h m hm, rw le_zero_iff.mp hm, exact ⟨c₁, h⟩ },
  { intros h m hm,
    cases hm with _ hm,
    { exact ⟨c₁, h⟩ },
    { obtain ⟨c₂, hc₂⟩ := (correct_multistep_succ_iff' _ _ _).mp h,
      refine IH _ hc₂.left m hm } }
end

theorem no_early_halt_of_correct_multistep {M : machine Γ Λ} {n c₀ c₁} : c₀[M]▸^[n]c₁ → ∀ m < n, ∃ c₂, c₀[M]▸^[m]c₂ ∧ ¬halted c₂ :=
begin
  intros h m hm,
  have := nat.add_sub_of_le (nat.add_one_le_iff.mpr hm),
  rw ← this at h,
  obtain ⟨c₂, hc₂⟩ := (correct_multistep_add_iff _ _ _ _).mp h,
  obtain ⟨c₃, hc₃⟩ := (correct_multistep_succ_iff' _ _ _).mp hc₂.left,
  exact ⟨_, ⟨hc₃.left, (exists_correct_step_iff_not_halted _).mp ⟨_, hc₃.right⟩⟩⟩
end

theorem reaches_iff_exists_multistep' {M : machine Γ Λ} (c₀ c₁) : reaches M c₀ c₁ ↔ ∃ n, c₁ = multistep' M n c₀ :=
begin
  split,
  { intro h,
    induction h with c₂ c₃ _ hc₃ IH,
    { exact ⟨0, rfl⟩ },
    { cases IH with n hc₂,
      use n + 1,
      rw [multistep'_succ', ← hc₂],
      exact hc₃ } },
  { rw forall_exists_index,
    intros n hn,
    induction n with n IH generalizing c₁,
    { simp [multistep'_zero, hn, reaches] },
    { rw multistep'_succ' at hn,
      exact relation.refl_trans_gen.tail (IH _ rfl) hn } }
end

theorem reaches_iff_correct_multistep {M : machine Γ Λ} (c₀ c₁ : cfg Γ Λ) : reaches M c₀ c₁ ↔ ∃ n, c₀[M]▸^[n]c₁ :=
by simp [reaches_iff_exists_multistep', correct_multistep]; tauto

end

section map
variables {Γ : Type*} [inhabited Γ]
variables {Γ' : Type*} [inhabited Γ']
variables {Λ : Type*} [inhabited Λ]
variables {Λ' : Type*} [inhabited Λ']

def stmt.map (f : turing.pointed_map Γ Γ') (g : Λ → Λ') : stmt Γ Λ → stmt Γ' Λ' :=
λ ⟨a, d, q⟩, (f a, d, q.map g)

def cfg.map (f : turing.pointed_map Γ Γ') (g : Λ → Λ') : cfg Γ Λ → cfg Γ' Λ' :=
λ ⟨q, T⟩, ⟨q.map g, T.map f⟩

variables (M : machine Γ Λ)
  (f₁ : turing.pointed_map Γ Γ') (f₂ : turing.pointed_map Γ' Γ) (g₁ : Λ → Λ') (g₂ : Λ' → Λ)

def machine.map : machine Γ' Λ' :=
λ q l, (M (g₂ q) (f₂ l)).map f₁ g₁

theorem machine.map_step {S : set Λ} (f₂₁ : function.right_inverse f₁ f₂) (g₂₁ : ∀ q ∈ S, g₂ (g₁ q) = q) :
  ∀ c : cfg Γ Λ, c.q.elim true S → (step M c).map (cfg.map f₁ g₁) = step (M.map f₁ f₂ g₁ g₂) (cfg.map f₁ g₁ c) :=
begin
  rintro ⟨_|⟨q⟩, T⟩ h,
  { refl },
  { simp [step, machine.map, cfg.map, f₂₁ _, g₂₁ q h],
    rcases M q T.head with ⟨a, d, q'⟩,
    simp [step, cfg.map, turing.tape.map_move f₁],
    refl }
end

theorem map_init (g₁ : turing.pointed_map Λ Λ') (l : list Γ) : (init l).map f₁ g₁ = init (l.map f₁) :=
congr (congr_arg _ (eq.trans (option.map_some') (congr_arg _ g₁.map_pt))) (turing.tape.map_mk₁ _ _)

end map

end BB