import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
--import Mathlib.Ring_theory.Non_zero_divisors
--import Mathlib.Algebra.Group.basic


 /-
import analysis.calculus.deriv analysis.special_functions.exp_deriv ring_theory.non_zero_divisors algebra.group.basic

analysis.calculus.deriv contains definitions and theorems about derivatives
analysis.special_functions.exp_deriv contains definitions and theorems about the exponential function and its derivatives
ring_theory.non_zero_divisors contains definitions and theorems about domains (of which ℝ is one)
algebra.group.basic contains definitions and theorems about groups (of which ℝ is one)
-/

open Real

noncomputable def D (f : ℝ → ℝ) : ℝ → ℝ :=
  λ x : ℝ => deriv f x

/-
the derivative is defined in Lean differently than the derivative in a usual calculus class
this definition above treats the derivative as an operator on functions
it was easier to formalize the theorem in Lean with the derivative as we expect it
-/

lemma D_add {f g : ℝ → ℝ} (df : Differentiable ℝ f) (dg : Differentiable ℝ g) : D (f + g) = D f + D g := --capitalized 'differentible'
  funext (λ x => calc
      _ = deriv (λ y : ℝ => f y + g y) x := by rfl
      _ = deriv f x + deriv g x := by exact deriv_add (df x) (dg x))


lemma D_mul {f g : ℝ → ℝ} (df : Differentiable ℝ f) (dg : Differentiable ℝ g) : D (f * g) = D f * g + f * D g :=
  funext (λ x => calc
      _ = deriv (λ y : ℝ=> f y * g y) x           := by rfl
      -- this line is necessary for some reason
      _ = (deriv f x) * g x + (f x) * deriv g x   := by rw [deriv_mul (df x) (dg x)])

lemma second_D_mul {f g : ℝ → ℝ} (df : Differentiable ℝ f) (d₂f : Differentiable ℝ (D f)) (dg : Differentiable ℝ g) (d₂g : Differentiable ℝ (D g)) :
D (D (f * g)) = D (D f) * g + 2 * D f * D g + f * D (D g) :=
  let f' := D f
  let f'' := D f'
  let g' := D g
  let g'' := D g'

  have h₁ : Differentiable ℝ (f' * g) := Differentiable.mul d₂f dg

  have h₂ :Differentiable ℝ (f * g') := Differentiable.mul df d₂g

  show D (D (f * g)) = f'' * g + 2 * f' * g' + f * g'' from
    calc
      D (D (f * g)) = D (f' * g + f * g') := by rw [D_mul df dg]
      _ = D (f' * g) + D (f * g') := by rw [D_add h₁ h₂]
      --_ = f''*g+2*f'*g'+f*g'' := by sorry
      _ = f'' * g + f' * g' + D (f * g') := by rw [D_mul d₂f dg]
      _ = f'' * g + f' * g' + (f' * g' + f * g'') := by rw [D_mul df d₂g]
      _ = f'' * g + f' * g' + f' * g' + f * g'' := by rw [add_assoc (f'' * g + f' * g') (f' * g') (f * g'')]
      _ = f'' * g + 2 * (f' * g') + f * g'' := by rw [two_mul (f' * g'), add_assoc (f'' * g) (f' * g') (f' * g')]
      _ = f'' * g + 2 * f' * g' + f * g'' := by rw [mul_assoc 2 f' g']

lemma exp_D {f : ℝ → ℝ} (df : Differentiable ℝ f) : D (λ x : ℝ => exp (f x)) = λ x : ℝ => exp (f x) * D f x := funext (λ x => deriv_exp (df x))

lemma const_mul_D (a : ℝ) : D (λ x : ℝ => a * x) = λ _ : ℝ => a :=
  have h₁ : ∀ x : ℝ, (a * id x = (λ y : ℝ => a * y) x) := by
    intro z
    rw [id.def]

  funext (λ y => (calc
      _ = deriv (λ x : ℝ => a * x) y                    := by rfl
    _ = deriv (λ x : ℝ => a * (id x)) y               := by rw [(funext h₁)]
    _ = a * (deriv id y)                            := by rw[(deriv_const_mul a (differentiable_id y) )]
    _ = a * 1                                       := by rw [deriv_id]
    _ = a                                           := by rw [mul_one]))


def redington (f : ℝ → ℝ) (x : ℝ) : Prop := f x = 0 ∧ D f x = 0 ∧ D (D f) x > 0
/-
this definition defines what it means for a function to satisfy Redington immunization at a point
-/

lemma redington_implies {f : ℝ → ℝ} {x : ℝ} (h0: f x = 0) (h1: D f x = 0)  (h2:D (D f) x > 0) : redington f x :=
  And.intro h0 (And.intro h1 h2)
/-
this lemma rewrites the conditions for satisfying Redington immunization as nested conditional statements instead of a nested conjunction; a form of "currying"
-/

lemma hf2_justification  {f g₀ : ℝ → ℝ} {δ : ℝ}
(df : Differentiable ℝ f) (dg₀ : Differentiable ℝ g₀) (hf : f δ = 0) (hg₀ : 0 < g₀ δ)
(hg : (D (f * g₀)) δ = 0) :
(D f) δ = 0 :=

  let g := (f * g₀)
  have h₁ : D g = D f * g₀ + f * D g₀ := by apply (D_mul df dg₀)
  have h₂ : D f δ * g₀ δ + f δ * D g₀ δ = D g δ := by exact
    (congrFun h₁ δ).symm

  have h₃ : D f δ * g₀ δ = 0 := by rw [hf] at h₂; simp at h₂; rw [hg] at h₂; rw [h₂]

  have g₀_ne_zero : g₀ δ ≠ 0 := by exact ne_of_gt hg₀

  eq_zero_of_ne_zero_of_mul_right_eq_zero g₀_ne_zero h₃

lemma d₂g_form_simplified_justification {f g₀ : ℝ → ℝ} {δ : ℝ}
(df : Differentiable ℝ f) (d₂f : Differentiable ℝ (D f))
(dg₀ : Differentiable ℝ g₀) (d₂g₀ : Differentiable ℝ (D g₀)) (hf : f δ = 0) (hf' : (D f) δ = 0) :
(D (D (f * g₀))) δ = (D (D f)) δ * g₀ δ :=

  show (D (D (f * g₀))) δ = (D (D f)) δ * g₀ δ by
  calc
    (D (D (f * g₀))) δ = (D (D f) * g₀    + 2 * D f * D g₀     + f * D (D g₀)) δ   := congrFun (second_D_mul df d₂f dg₀ d₂g₀) δ
    _ = D (D f) δ * g₀ δ + 2 * D f δ * D g₀ δ + f δ * D (D g₀) δ  := by rfl
    _ = D (D f) δ * g₀ δ + 2 * D f δ * D g₀ δ +   0 * D (D g₀) δ  := by rw [hf]
    _ = D (D f) δ * g₀ δ + 2 * 0     * D g₀ δ +   0 * D (D g₀) δ  := by rw [hf']
    _ = (D (D f)) δ * g₀ δ := by ring

lemma hf1_justification  {f g₀ : ℝ → ℝ} {δ : ℝ}
  (hg : (f * g₀) δ = 0) (g₀_pos : 0 < g₀ δ):
  f δ = 0 :=
  have h₁ : f δ * g₀ δ = 0 := by apply Eq.symm; rw [←hg]; rfl
  have g₀_ne_zero : g₀ δ ≠ 0 := ne_of_gt g₀_pos
  eq_zero_of_ne_zero_of_mul_right_eq_zero g₀_ne_zero h₁

theorem g_form_implies_redington_f_iff_g {f : ℝ → ℝ} {t δ: ℝ}
  (df : Differentiable ℝ f)
  (d₂f : Differentiable ℝ (D f)):
  let g := λ x : ℝ => (f x) * exp (t * x)
  (redington f δ ↔ redington g δ) :=
  -- these lines allow me to use shorthands for pieces of the function g and shorthands for derivatives
  let g := λ x : ℝ => (f x) * exp (t * x)
  let g₀_arg   := λ x : ℝ => t * x
  --let g₀_arg'  := D g₀_arg
  let g₀       := λ x : ℝ=> exp (t * x)
  --let g₀'      := D g₀
  --let g₀''     := D g₀'
  let f'       := D f
  let f''      := D f'
  let g'       := D g
  let g''      := D g'

  have g_form_at_δ : g δ = (f δ) * (g₀ δ) := rfl

  -- these "have" statements prove a bunch of facts about the differentiability of pieces of g
  have dg₀_arg : Differentiable ℝ g₀_arg := Differentiable.const_mul (differentiable_id) t

  have dg₀ : Differentiable ℝ g₀ := Differentiable.exp dg₀_arg

  have dg₀_arg_form : D g₀_arg = λ _ : ℝ => t := by rw [const_mul_D t]

  have dg₀_form_lemma : ∀ y : ℝ, (λ (x : ℝ) => exp (g₀_arg x) * (λ (_ : ℝ) => t) x) y = (λ (x : ℝ) => t * exp (t * x)) y := by
    intro y
    exact mul_comm (exp (g₀_arg y)) ((λ _ => t) y)

  have dg₀_form : D g₀ = λ x : ℝ => t * exp (t * x) := by rw [exp_D dg₀_arg]; rw [dg₀_arg_form]; exact funext dg₀_form_lemma

  have d₂g₀ : Differentiable ℝ (D g₀) := by rw [dg₀_form]; apply Differentiable.mul (differentiable_const t) (dg₀)

  have g₀_pos : 0 < g₀ δ := exp_pos (t * δ)

  /-
  from here, two main "have" statements are proved: one establishes the forward direction of the proof, and the other the reverse
  -/

  -- proving the forward direction
  have forward_dir : redington f δ → redington g δ := by
    intro hf;

    -- these three lines are from the premise that f satisfies Redington immunization at δ
    have hf1 : f δ = 0 := hf.1;
    have hf2 : f' δ = 0 := hf.2.1;
    have hf3 : f'' δ > 0 := hf.2.2;

    -- these statements prove that g satisfies the three conditions for Redington immunization at δ

    have hg1 : g δ = 0 := by rw [g_form_at_δ]; rw [hf1]; rw [zero_mul]

    have hg2 : g' δ = 0 := by
      calc
      g' δ = D g δ                           := by rfl
      _ = D (f * g₀) δ                     := by {rfl}
      _ = (D f * g₀ + f * D g₀) δ          := by rw[D_mul df dg₀]
      _ = (D f) δ * g₀ δ + f δ * (D g₀) δ  := by simp
      _ = 0 * g₀ δ + f δ * (D g₀) δ        := by rw [← hf2]
      _ = 0 * g₀ δ + 0 * (D g₀) δ          := by rw [hf1]
      _ = 0 + 0 := by repeat rw[zero_mul]
      _ = 0 := by rw[add_zero]

    have d₂g_form_simplified : g'' δ = f'' δ * g₀ δ := d₂g_form_simplified_justification df d₂f dg₀ d₂g₀ hf1 hf2

    have hg3 : 0 < g'' δ := by rw [d₂g_form_simplified]; apply mul_pos hf3 g₀_pos

    exact redington_implies hg1 hg2 hg3-- this line uses the previous "have" statements to finish the proof of the forward direction

  -- proving the reverse direction
  have reverse_dir : redington g δ → redington f δ := by
    intro hg;

    have hg3 : g'' δ > 0 := hg.2.2;

    -- these statements prove that f satisfies the three conditions for Redington immunization at δ

    have hf1 : f δ = 0 := hf1_justification hg.1 g₀_pos;

    have hf2 : f' δ = 0 := hf2_justification df dg₀ hf1 g₀_pos hg.2.1

    have d₂g_form_simplified : g'' δ = f'' δ * g₀ δ :=
      d₂g_form_simplified_justification df d₂f dg₀ d₂g₀ hf1 hf2

    have hf3 : f'' δ > 0 := by
      rw [d₂g_form_simplified] at hg3;
      exact (zero_lt_mul_right g₀_pos).mp hg3--apply?-- pos_of_mul_pos_left (gt.lt hg3) (le_of_lt g₀_pos)


    exact redington_implies hf1 hf2 hf3 -- this line uses the previous "have" statements to finish the proof of the reverse direction

  by exact {mp := forward_dir, mpr := reverse_dir}
  --iff.intro forward_dir reverse_dir -- this line combines the proof of the forward and reverse directions to finish the proof of the theorem
