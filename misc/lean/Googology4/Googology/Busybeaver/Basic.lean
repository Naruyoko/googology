import Googology.Busybeaver.Defs

#align_import busybeaver.basic

namespace BB

section

variable {Γ Λ : Type _} [Inhabited Γ] [Inhabited Λ]

@[simp]
theorem multistep'_zero {M : Machine Γ Λ} {c} : multistep' M 0 c = c :=
  rfl

theorem multistep'_succ {M : Machine Γ Λ} {n c} :
    multistep' M (n + 1) c = multistep' M n (step' M c) :=
  rfl

theorem multistep'_succ' {M : Machine Γ Λ} {n c} :
    multistep' M (n + 1) c = step' M (multistep' M n c) :=
  Function.iterate_succ_apply' (step' M) n c

@[simp]
theorem multistep_zero {M : Machine Γ Λ} {c} : multistep M 0 c = c :=
  rfl

theorem multistep_succ {M : Machine Γ Λ} {n c} :
    multistep M (n + 1) c = multistep' M n (step M c) :=
  rfl

theorem multistep_succ' {M : Machine Γ Λ} {n c} :
    multistep M (n + 1) c = step' M (multistep M n c) :=
  Function.iterate_succ_apply' (step' M) n c

theorem isSome_of_isSome_step' {M : Machine Γ Λ} {c} : (step' M c).isSome → c.isSome :=
  by
  repeat' rw [Option.isSome_iff_exists]
  simp [step']
  tauto

theorem isSome_of_isSome_multistep' {M : Machine Γ Λ} {n c} :
    (multistep' M n c).isSome → c.isSome :=
  by
  induction' n with n IH generalizing c
  · tauto
  · intro h
    exact is_some_of_is_some_step' (IH h)

@[simp, refl]
theorem correctMultistep_zero_iff_refl {M : Machine Γ Λ} (c₀ c₁) : c₀[M]▸^[0]c₁ ↔ c₀ = c₁ :=
  by
  constructor
  · intro h
    simp [correct_multistep] at h
    exact option.some_inj.mp h
  · exact congr_arg _

@[simp]
theorem correctMultistep_one_iff_correctStep {M : Machine Γ Λ} (c₀ c₁) : c₀[M]▸^[1]c₁ ↔ c₀[M]▸c₁ :=
  ⟨rfl.mp, congr_arg _⟩

theorem exists_correctStep_iff_not_halted {M : Machine Γ Λ} (c₀) : (∃ c₁, c₀[M]▸c₁) ↔ ¬Halted c₀ :=
  by constructor <;> rcases c₀ with ⟨_ | q, _⟩ <;> tauto

theorem correctMultistep_succ_iff {M : Machine Γ Λ} (n c₀ c₁) :
    c₀[M]▸^[n + 1]c₁ ↔ ∃ c₂, c₀[M]▸c₂ ∧ c₂[M]▸^[n]c₁ :=
  by
  simp [correct_multistep, multistep_succ]
  constructor
  · intro h
    obtain ⟨c₂, hc₂⟩ :=
      option.is_some_iff_exists.mp
        (is_some_of_is_some_multistep' (option.is_some_iff_exists.mpr ⟨_, h⟩))
    use c₂
    constructor
    · exact hc₂
    · rw [hc₂] at h
      exact h
  · intro h
    rcases h with ⟨c₂, ⟨h₁, h₂⟩⟩
    simp [correct_step] at h₁
    rw [h₁]
    exact h₂

theorem correctMultistep_add_iff {M : Machine Γ Λ} (m n c₀ c₁) :
    c₀[M]▸^[m + n]c₁ ↔ ∃ c₂, c₀[M]▸^[m]c₂ ∧ c₂[M]▸^[n]c₁ :=
  by
  induction' m with m IH generalizing c₀
  · simp
  · have : m + 1 + n = m + n + 1 := by finish
    rw [this]
    constructor
    · intro h
      obtain ⟨c₂, hc₂⟩ := (correct_multistep_succ_iff _ _ _).mp h
      obtain ⟨c₃, hc₃⟩ := (IH _).mp hc₂.right
      exact ⟨c₃, ⟨(correct_multistep_succ_iff _ _ _).mpr ⟨_, ⟨hc₂.left, hc₃.left⟩⟩, hc₃.right⟩⟩
    · intro h
      cases' h with c₂ hc₂
      obtain ⟨c₃, hc₃⟩ := (correct_multistep_succ_iff _ _ _).mp hc₂.left
      rw [correct_multistep_succ_iff]
      exact ⟨c₃, ⟨hc₃.left, (IH _).mpr ⟨c₂, ⟨hc₃.right, hc₂.right⟩⟩⟩⟩

theorem correctMultistep_succ_iff' {M : Machine Γ Λ} (n c₀ c₁) :
    c₀[M]▸^[n + 1]c₁ ↔ ∃ c₂, c₀[M]▸^[n]c₂ ∧ c₂[M]▸c₁ := by simp [correct_multistep_add_iff]

@[trans]
theorem correctStep_correst_step_trans_correctMultistep {M : Machine Γ Λ} (c₀ c₁ c₂) :
    c₀[M]▸c₁ → c₁[M]▸c₂ → c₀[M]▸^[2]c₂ := fun h₁ h₂ =>
  (correctMultistep_succ_iff _ _ _).mpr ⟨c₁, ⟨h₁, h₂⟩⟩

@[trans]
theorem correctMultistep_correst_step_trans {M : Machine Γ Λ} (n c₀ c₁ c₂) :
    c₀[M]▸^[n]c₁ → c₁[M]▸c₂ → c₀[M]▸^[n + 1]c₂ := fun h₁ h₂ =>
  (correctMultistep_succ_iff' _ _ _).mpr ⟨c₁, ⟨h₁, h₂⟩⟩

@[trans]
theorem correctStep_correst_multistep_trans {M : Machine Γ Λ} (n c₀ c₁ c₂) :
    c₀[M]▸c₁ → c₁[M]▸^[n]c₂ → c₀[M]▸^[n + 1]c₂ := fun h₁ h₂ =>
  (correctMultistep_succ_iff _ _ _).mpr ⟨c₁, ⟨h₁, h₂⟩⟩

@[trans]
theorem correst_multistep_trans {M : Machine Γ Λ} (m n c₀ c₁ c₂) :
    c₀[M]▸^[m]c₁ → c₁[M]▸^[n]c₂ → c₀[M]▸^[m + n]c₂ := fun h₁ h₂ =>
  (correctMultistep_add_iff _ _ _ _).mpr ⟨c₁, ⟨h₁, h₂⟩⟩

theorem exists_correctMultistep_le_of_correctMultistep {M : Machine Γ Λ} (n c₀ c₁) :
    c₀[M]▸^[n]c₁ → ∀ m ≤ n, ∃ c₂, c₀[M]▸^[m]c₂ :=
  by
  induction' n with n IH generalizing c₁
  · intro h m hm; rw [le_zero_iff.mp hm]; exact ⟨c₁, h⟩
  · intro h m hm
    cases' hm with _ hm
    · exact ⟨c₁, h⟩
    · obtain ⟨c₂, hc₂⟩ := (correct_multistep_succ_iff' _ _ _).mp h
      refine' IH _ hc₂.left m hm

theorem no_early_halt_of_correctMultistep {M : Machine Γ Λ} {n c₀ c₁} :
    c₀[M]▸^[n]c₁ → ∀ m < n, ∃ c₂, c₀[M]▸^[m]c₂ ∧ ¬Halted c₂ :=
  by
  intro h m hm
  have := Nat.add_sub_of_le (nat.add_one_le_iff.mpr hm)
  rw [← this] at h
  obtain ⟨c₂, hc₂⟩ := (correct_multistep_add_iff _ _ _ _).mp h
  obtain ⟨c₃, hc₃⟩ := (correct_multistep_succ_iff' _ _ _).mp hc₂.left
  exact ⟨_, ⟨hc₃.left, (exists_correct_step_iff_not_halted _).mp ⟨_, hc₃.right⟩⟩⟩

theorem reaches_iff_exists_multistep' {M : Machine Γ Λ} (c₀ c₁) :
    Reaches M c₀ c₁ ↔ ∃ n, c₁ = multistep' M n c₀ :=
  by
  constructor
  · intro h
    induction' h with c₂ c₃ _ hc₃ IH
    · exact ⟨0, rfl⟩
    · cases' IH with n hc₂
      use n + 1
      rw [multistep'_succ', ← hc₂]
      exact hc₃
  · rw [forall_exists_index]
    intro n hn
    induction' n with n IH generalizing c₁
    · simp [multistep'_zero, hn, reaches]
    · rw [multistep'_succ'] at hn
      exact Relation.ReflTransGen.tail (IH _ rfl) hn

theorem reaches_iff_correctMultistep {M : Machine Γ Λ} (c₀ c₁ : Cfg Γ Λ) :
    Reaches M c₀ c₁ ↔ ∃ n, c₀[M]▸^[n]c₁ := by
  simp [reaches_iff_exists_multistep', correct_multistep] <;> tauto

end

section Map

variable {Γ : Type _} [Inhabited Γ]

variable {Γ' : Type _} [Inhabited Γ']

variable {Λ : Type _} [Inhabited Λ]

variable {Λ' : Type _} [Inhabited Λ']

def Stmt.map (f : Turing.PointedMap Γ Γ') (g : Λ → Λ') : Stmt Γ Λ → Stmt Γ' Λ' := fun ⟨a, d, q⟩ =>
  (f a, d, q.map g)

def Cfg.map (f : Turing.PointedMap Γ Γ') (g : Λ → Λ') : Cfg Γ Λ → Cfg Γ' Λ' := fun ⟨q, T⟩ =>
  ⟨q.map g, T.map f⟩

variable (M : Machine Γ Λ) (f₁ : Turing.PointedMap Γ Γ') (f₂ : Turing.PointedMap Γ' Γ) (g₁ : Λ → Λ')
  (g₂ : Λ' → Λ)

def Machine.map : Machine Γ' Λ' := fun q l => (M (g₂ q) (f₂ l)).map f₁ g₁

theorem Machine.map_step {S : Set Λ} (f₂₁ : Function.RightInverse f₁ f₂)
    (g₂₁ : ∀ q ∈ S, g₂ (g₁ q) = q) :
    ∀ c : Cfg Γ Λ,
      c.q.elim True S →
        (step M c).map (Cfg.map f₁ g₁) = step (M.map f₁ f₂ g₁ g₂) (Cfg.map f₁ g₁ c) :=
  by
  rintro ⟨_ | ⟨q⟩, T⟩ h
  · rfl
  · simp [step, machine.map, cfg.map, f₂₁ _, g₂₁ q h]
    rcases M q T.head with ⟨a, d, q'⟩
    simp [step, cfg.map, Turing.Tape.map_move f₁]
    rfl

theorem map_init (g₁ : Turing.PointedMap Λ Λ') (l : List Γ) :
    (init l).map f₁ g₁ = init (l.map f₁) :=
  congr (congr_arg _ (Eq.trans Option.map_some' (congr_arg _ g₁.map_pt))) (Turing.Tape.map_mk₁ _ _)

end Map

end BB

