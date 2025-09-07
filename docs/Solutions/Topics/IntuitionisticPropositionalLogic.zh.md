```lean
import GlimpseOfLean.Library.Basic
open Set

namespace IntuitionisticPropositionalLogic

```

让我们尝试实现一种直觉主义命题逻辑的语言。

这个文件假设你已经知道什么是直觉主义逻辑以及什么是 Heyting 代数。注意，还有一个经典逻辑版本的文件：`ClassicalPropositionalLogic.lean`，它没有这样的先决条件（但仍然假设你对建立逻辑框架感兴趣）。

```lean
def Variable : Type := ℕ

```

我们定义命题公式，以及它们的一些记号。

```lean
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

```

接下来我们定义 Heyting 代数语义。

在 Heyting 代数 `H` 中取值的赋值就是从变量到 `H` 的映射让我们定义如何在命题公式上计算赋值。

```lean
variable {H : Type*} [HeytingAlgebra H]
@[simp]
def eval (φ : Variable → H) : Formula → H
  | bot    => ⊥
  | # P    => φ P
  | A || B => eval φ A ⊔ eval φ B
  | A && B => eval φ A ⊓ eval φ B
  | A ⇒ B => eval φ A ⇨ eval φ B

```

我们说 `A` 是 `Γ` 的结论，如果对于任何 Heyting 代数中的所有赋值，如果对于所有 `B ∈ Γ`，`eval φ B` 都在某个元素之上，那么 `eval φ A` 也在这个元素之上。注意，对于有限集合 `Γ`，这恰好对应于 `Infimum { eval φ B | B ∈ Γ } ≤ eval φ A`。这个有效性定义的"米田化"版本使用起来非常方便。

```lean
def Models (Γ : Set Formula) (A : Formula) : Prop :=
  ∀ {H : Type} [HeytingAlgebra H] {φ : Variable → H} {c}, (∀ B ∈ Γ, c ≤ eval φ B) → c ≤ eval φ A

local infix:27 (priority := high) " ⊨ " => Models
def Valid (A : Formula) : Prop := ∅ ⊨ A

```

这里是有效性的一些基本性质。

策略 `simp` 将自动简化标记了 `@[simp]` 的定义，并使用标记了 `@[simp]` 的定理进行重写。

```lean
variable {φ : Variable → H} {A B : Formula}
@[simp] lemma eval_neg : eval φ ~A = (eval φ A)ᶜ := by simp [neg]

@[simp] lemma eval_top : eval φ top = ⊤ := by
  -- sorry
  simp [top]
  -- sorry

@[simp]
lemma isTrue_equiv : eval φ (A ⇔ B) = (eval φ A ⇨ eval φ B) ⊓ (eval φ B ⇨ eval φ A) := by
  -- sorry
  simp [equiv]
  -- sorry

```

作为练习，让我们证明下面的命题，它在直觉主义逻辑中成立。

```lean
example : Valid (~(A && ~A)) := by
  -- sorry
  simp [Valid, Models]
  -- sorry

```

让我们定义关于直觉主义逻辑的可证性。

```lean
section
set_option hygiene false -- this is a hacky way to allow forward reference in notation
local infix:27 " ⊢ " => ProvableFrom


```

`Γ ⊢ A` 是一个谓词，表示存在一个以 `A` 为结论、以 `Γ` 中的假设为前提的证明树。这是直觉主义逻辑自然演绎的典型规则列表。

```lean
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

```

为了练习使用证明系统，让我们证明下面的内容。你可以使用前面几行定义的 `apply_ax` 策略，它证明一个可以使用 `ax` 规则证明的目标。或者你可以手动进行，使用下面关于插入的引理。
```
  mem_insert x s : x ∈ insert x s
  mem_insert_of_mem y : x ∈ s → x ∈ insert y s
```

```lean
example : Provable ((~A || ~B) ⇒ ~(A && B)) := by
  -- sorry
  apply impI
  apply impI
  apply orE (by apply_ax)
  · apply impE (by apply_ax)
    apply andE1 (by apply_ax)
  · apply impE (by apply_ax)
    apply andE2 (by apply_ax)
  -- sorry

```

可选练习

```lean
example : Provable (~(A && ~A)) := by
  -- sorry
  apply impI
  exact impE (andE2 (by apply_ax)) (andE1 (by apply_ax))
  -- sorry

```

可选练习

```lean
example : Provable ((~A && ~B) ⇒ ~(A || B)) := by
  -- sorry
  apply impI
  apply impI
  apply orE (by apply_ax)
  · exact impE (andE1 (by apply_ax)) (by apply_ax)
  · exact impE (andE2 (by apply_ax)) (by apply_ax)
  -- sorry

```

你可以使用 `induction` 对 `h` 进行证明。你需要告诉 Lean 你想要同时对所有 `Δ` 证明，使用 `induction h generalizing Δ`。如果你不明确命名，Lean 将把创建的假设标记为不可访问（用 † 标记）。你可以使用例如 `rename_i ih` 或 `rename_i A B h ih` 来命名最后的不可访问变量。或者你可以使用 `case impI ih => <proof>` 来证明特定情况。你可能需要使用引理 `insert_subset_insert : s ⊆ t → insert x s ⊆ insert x t`。

```lean
lemma weakening (h : Γ ⊢ A) (h2 : Γ ⊆ Δ) : Δ ⊢ A := by
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

```

使用 `apply?` 策略来找到声明 `Γ ⊆ insert x Γ` 的引理。你可以点击右侧面板中的蓝色建议来自动应用建议。

```lean
lemma ProvableFrom.insert (h : Γ ⊢ A) : insert B Γ ⊢ A := by
  -- sorry
  apply weakening h
  -- use `apply?` here
  exact subset_insert B Γ
  -- sorry

```

证明演绎定理现在很容易了。

```lean
lemma deduction_theorem (h : Γ ⊢ A) : insert (A ⇒ B) Γ ⊢ B := by
  -- sorry
  apply impE (ax $ mem_insert _ _)
  exact h.insert
  -- sorry

lemma Provable.mp (h1 : Provable (A ⇒ B)) (h2 : Γ ⊢ A) : Γ ⊢ B := by
  -- sorry
  apply impE _ h2
  apply weakening h1
  -- apply?
  exact empty_subset Γ
  -- sorry

```

这很棘手，因为你需要使用 Heyting 代数中的运算进行计算。

```lean
set_option maxHeartbeats 0 in
theorem soundness_theorem (h : Γ ⊢ A) : Γ ⊨ A := by
  -- sorry
  induction h <;> intros H hH φ c hφ
  solve_by_elim
  case impI ih =>
    simp
    apply ih
    simp
    intros B hB
    -- apply?
    exact inf_le_of_left_le (hφ B hB)
  case impE ih₁ ih₂ =>
    specialize ih₁ hφ
    simp at ih₁
    rwa [inf_eq_left.mpr (ih₂ hφ)] at ih₁
  case andI ih₁ ih₂ => simp [ih₁ hφ, ih₂ hφ]
  case andE1 ih =>
    specialize ih hφ
    simp at ih
    exact ih.1
  case andE2 ih =>
    specialize ih hφ
    simp at ih
    exact ih.2
  case orI1 ih =>
    simp
    exact le_trans (ih hφ) le_sup_left
  case orI2 ih =>
    simp
    exact le_trans (ih hφ) le_sup_right
  case orE Γ A B C _h1 _h2 _h3 ih₁ ih₂ ih₃ =>
    specialize ih₁ hφ
    have h2φ : ∀ D ∈ insert A Γ, c ⊓ eval φ A ≤ eval φ D := by
      simp; intros D hD; exact inf_le_of_left_le (hφ D hD) -- apply? found this
    have h3φ : ∀ D ∈ insert B Γ, c ⊓ eval φ B ≤ eval φ D := by
      simp; intros D hD; exact inf_le_of_left_le (hφ D hD) -- apply? found this
    simp at ih₁
    rw [← inf_eq_left.mpr ih₁, inf_sup_left]
    rw [← sup_idem (a := eval φ C)]
    exact sup_le_sup (ih₂ h2φ) (ih₃ h3φ)
  case botE ih =>
    specialize ih hφ
    simp at ih
    simp [ih]
  -- sorry

theorem valid_of_provable (h : Provable A) : Valid A := by
  -- sorry
  exact soundness_theorem h
  -- sorry

```

  如果你愿意，现在可以尝试一些这些更长的项目。

  1. 定义 Kripke 语义并证明关于 Kripke 语义的可靠性。

  2. 证明关于 Heyting 代数语义或 Kripke 语义的完备性。


```lean
end IntuitionisticPropositionalLogic

```