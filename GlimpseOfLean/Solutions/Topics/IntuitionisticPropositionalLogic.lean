

import GlimpseOfLean.Library.Basic
open Set

namespace IntuitionisticPropositionalLogic

/- 我们试图实现直觉主义命题逻辑的语言。

注意，这个文件也有一个经典逻辑版本：`ClassicalPropositionalLogic.lean`
-/

def Variable : Type := ℕ

/- 我们定义了命题公式，并为它们制定了一些符号表示法。
-/

inductive Formula : Type where
  | var : Variable → Formula
  | bot : Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  | impl : Formula → Formula → Formula

open Formula
local notation:max (priority := high) "#" x:max => var x
local infix:30 (priority := high) " || " => disj
local infix:35 (priority := high) " && " => conj
local infix:28 (priority := high) " ⇒ " => impl

def neg (A : Formula) : Formula := A ⇒ bot
local notation:(max+2) (priority := high) "~" x:max => neg x
def top := ~bot
def equiv (A B : Formula) : Formula := (A ⇒ B) && (B ⇒ A)
local infix:29 (priority := high) " ⇔ " => equiv

/- 接下来我们定义海廷代数语义学。

在海廷代数`H`中的估值只是一个从变量到`H`的映射
我们来定义如何对命题公式进行估值评估。
-/

variable {H : Type _} [HeytingAlgebra H]
@[simp]
def eval (v : Variable → H) : Formula → H
  | bot    => ⊥
  | # P    => v P
  | A || B => eval v A ⊔ eval v B
  | A && B => eval v A ⊓ eval v B
  | A ⇒ B => eval v A ⇨ eval v B

/- 我们称 `A` 是 `Γ` 的一个推断，如果对于任何 Heyting 代数中的所有取值，如果 `eval v B` 对于所有 `B ∈ Γ` 都高于某个元素，那么 `eval v A` 也高于这个元素。注意，对于有限集 `Γ`，这正好对应于 `Infimum { eval v B | B ∈ Γ } ≤ eval v A`。这个 "yoneda'd" 版本的有效性定义非常方便我们使用。
-/

def Models (Γ : Set Formula) (A : Formula) : Prop :=
  ∀ {H : Type} [HeytingAlgebra H] {v : Variable → H} {c}, (∀ B ∈ Γ, c ≤ eval v B) → c ≤ eval v A

local infix:27 (priority := high) " ⊨ " => Models
def Valid (A : Formula) : Prop := ∅ ⊨ A

/- 下面是一些有效性的基本属性。

  `simp` 策略会自动简化标记为 `@[simp]` 的定义，并使用标记为 `@[simp]` 的定理进行重写。
-/

variable {v : Variable → H} {A B : Formula}
@[simp] lemma eval_neg : eval v ~A = (eval v A)ᶜ := by simp

@[simp] lemma eval_top : eval v top = ⊤ := by {
  -- sorry
  simp
  -- sorry
}

@[simp]
lemma isTrue_equiv : eval v (A ⇔ B) = (eval v A ⇨ eval v B) ⊓ (eval v B ⇨ eval v A) := by {
  -- sorry
  simp
  -- sorry
}

/- 作为一个练习，我们来证明以下命题，这在直观逻辑中是成立的。
-/

example : Valid (~(A && ~A)) := by {
  -- sorry
  simp [Valid, Models]
  -- sorry
}

/- 让我们以直觉逻辑来定义可证明性。
-/

section
set_option hygiene false -- this is a hacky way to allow forward reference in notation
local infix:27 " ⊢ " => ProvableFrom

/- `Γ ⊢ A` 是一个谓词，表示有一个以 `A` 作为结论的证明树，其假设来自于 `Γ`。这是直觉主义逻辑自然演绎的典型规则列表。
-/

inductive ProvableFrom : Set Formula → Formula → Prop
  | ax    : ∀ {Γ A},   A ∈ Γ   → Γ ⊢ A
  | impI  : ∀ {Γ A B},  insert A Γ ⊢ B                → Γ ⊢ A ⇒ B
  | impE  : ∀ {Γ A B},           Γ ⊢ (A ⇒ B) → Γ ⊢ A  → Γ ⊢ B
  | andI  : ∀ {Γ A B},           Γ ⊢ A       → Γ ⊢ B  → Γ ⊢ A && B
  | andE1 : ∀ {Γ A B},           Γ ⊢ A && B           → Γ ⊢ A
  | andE2 : ∀ {Γ A B},           Γ ⊢ A && B           → Γ ⊢ B
  | orI1  : ∀ {Γ A B},           Γ ⊢ A                → Γ ⊢ A || B
  | orI2  : ∀ {Γ A B},           Γ ⊢ B                → Γ ⊢ A || B
  | orE   : ∀ {Γ A B C}, Γ ⊢ A || B → insert A Γ ⊢ C → insert B Γ ⊢ C → Γ ⊢ C
  | botE  : ∀ {Γ A},             Γ ⊢ bot              → Γ ⊢ A

end

local infix:27 (priority := high) " ⊢ " => ProvableFrom
def Provable (A : Formula) := ∅ ⊢ A

export ProvableFrom (ax impI impE botE andI andE1 andE2 orI1 orI2 orE)
variable {Γ Δ : Set Formula}

syntax "solve_mem" : tactic
syntax "apply_ax" : tactic
macro_rules
  | `(tactic| solve_mem) => `(tactic| first | apply mem_insert | apply mem_insert_of_mem; solve_mem)
  | `(tactic| apply_ax)  => `(tactic| { apply ax; solve_mem })

/- 为了熟悉证明系统，让我们证明以下内容。
  你可以使用前面定义的 `apply_ax` 策略，该策略可以证明一个可以通过 `ax` 规则证明的目标。
  或者你可以手动操作，使用以下关于插入的引理。
```
  mem_insert x s : x ∈ insert x s
  mem_insert_of_mem y : x ∈ s → x ∈ insert y s
```
-/

example : Provable ((~A || ~B) ⇒ ~(A && B)) := by {
  -- sorry
  apply impI
  apply impI
  apply orE (by apply_ax)
  · apply impE (by apply_ax)
    apply andE1 (by apply_ax)
  · apply impE (by apply_ax)
    apply andE2 (by apply_ax)
  -- sorry
}

/- 可选练习
-/

example : Provable (~(A && ~A)) := by {
  -- sorry
  apply impI
  exact impE (andE2 (by apply_ax)) (andE1 (by apply_ax))
  -- sorry
}

/- 可选练习
-/

example : Provable ((~A && ~B) ⇒ ~(A || B)) := by {
  -- sorry
  apply impI
  apply impI
  apply orE (by apply_ax)
  · exact impE (andE1 (by apply_ax)) (by apply_ax)
  · exact impE (andE2 (by apply_ax)) (by apply_ax)
  -- sorry
}

/- 你可以使用 `归纳法` 在 `h` 上进行以下证明。你可能会希望告诉 Lean ，你希望同时为所有的 `Δ` 进行证明，可以使用 `induction h generalizing Δ` 来实现。
  Lean 会将你没有明确命名的假设标记为不可访问（用 † 标记）。
  例如你可以使用 `rename_i ih` 或 
  `rename_i A B h ih` 来为最后的不可访问变量命名。或者你可以使用 `case impI ih => <proof>` 来证明特定的情况。
  你可能需要使用这个引理
  `insert_subset_insert : s ⊆ t → insert x s ⊆ insert x t`。
-/

lemma weakening (h : Γ ⊢ A) (h2 : Γ ⊆ Δ) : Δ ⊢ A := by {
  -- sorry
  induction h generalizing Δ
  case ax => apply ax; solve_by_elim
  case impI ih => apply impI; solve_by_elim [insert_subset_insert]
  case impE ih₁ ih₂ => apply impE <;> solve_by_elim
  case andI ih₁ ih₂ => apply andI <;> solve_by_elim
  case andE1 ih => apply andE1 <;> solve_by_elim
  case andE2 ih => apply andE2 <;> solve_by_elim
  case orI1 ih => apply orI1; solve_by_elim
  case orI2 ih => apply orI2; solve_by_elim
  case orE ih₁ ih₂ ih₃ => apply orE <;> solve_by_elim [insert_subset_insert]
  case botE ih => apply botE; solve_by_elim [insert_subset_insert]
  -- sorry
}

/- 使用 `apply?` 策略来找到陈述 `Γ ⊆ insert x Γ` 的引理。
  你可以点击右侧面板中的蓝色建议，来自动应用这个建议。
-/

lemma ProvableFrom.insert (h : Γ ⊢ A) : insert B Γ ⊢ A := by {
  -- sorry
  apply weakening h
  -- use `apply?` here
  exact subset_insert B Γ
  -- sorry
}

/- 现在，证明演绎定理变得十分简单。
-/

lemma deduction_theorem (h : Γ ⊢ A) : insert (A ⇒ B) Γ ⊢ B := by {
  -- sorry
  intros
  apply impE (ax $ mem_insert _ _)
  exact h.insert
  -- sorry
}

lemma Provable.mp (h1 : Provable (A ⇒ B)) (h2 : Γ ⊢ A) : Γ ⊢ B := by {
  -- sorry
  apply impE _ h2
  apply weakening h1
  -- apply?
  exact empty_subset Γ
  -- sorry
}

/- 这个问题有些棘手，因为你需要使用 Heyting 代数中的运算进行计算。
-/

set_option maxHeartbeats 0 in
theorem soundness_theorem (h : Γ ⊢ A) : Γ ⊨ A := by {
  -- sorry
  induction h <;> intros H hH v c hv
  solve_by_elim
  case impI ih =>
    simp
    apply ih
    simp
    intros B hB
    -- apply?
    exact inf_le_of_left_le (hv B hB)
  case impE ih₁ ih₂ =>
    specialize ih₁ hv
    simp at ih₁
    rwa [inf_eq_left.mpr (ih₂ hv)] at ih₁
  case andI ih₁ ih₂ => simp [ih₁ hv, ih₂ hv]
  case andE1 ih =>
    specialize ih hv
    simp at ih
    exact ih.1
  case andE2 ih =>
    specialize ih hv
    simp at ih
    exact ih.2
  case orI1 ih =>
    simp
    exact le_trans (ih hv) le_sup_left
  case orI2 ih =>
    simp
    exact le_trans (ih hv) le_sup_right
  case orE Γ A B C _h1 _h2 _h3 ih₁ ih₂ ih₃ =>
    specialize ih₁ hv
    have h2v : ∀ D ∈ insert A Γ, c ⊓ eval v A ≤ eval v D
    · simp; intros D hD; exact inf_le_of_left_le (hv D hD) -- apply? found this
    have h3v : ∀ D ∈ insert B Γ, c ⊓ eval v B ≤ eval v D
    · simp; intros D hD; exact inf_le_of_left_le (hv D hD) -- apply? found this
    simp at ih₁
    rw [← inf_eq_left.mpr ih₁, inf_sup_left]
    rw [← sup_idem (a := eval v C)]
    exact sup_le_sup (ih₂ h2v) (ih₃ h3v)
  case botE ih =>
    specialize ih hv
    simp at ih
    simp [ih]
  -- sorry
}

theorem valid_of_provable (h : Provable A) : Valid A := by {
  -- sorry
  exact soundness_theorem h
  -- sorry
}

/-   如果你愿意，现在可以尝试一些更长的项目。

  1. 定义 Kripke 语义并证明相对于 Kripke 语义的正确性。

  2. 对 Heyting 代数语义或 Kripke 语义证明完备性。
-/

end IntuitionisticPropositionalLogic

/- 
-/