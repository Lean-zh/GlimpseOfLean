```lean
import GlimpseOfLean.Library.Basic
open Set

namespace IntuitionisticPropositionalLogic
```

让我们尝试实现一种直觉主义命题逻辑的语言。

注意，这个文件还有一个经典逻辑的版本：`ClassicalPropositionalLogic.lean`

```lean
def Variable : Type := ℕ
```

我们定义了命题公式，以及一些表示符号。

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

接下来，我们定义 Heyting 代数语义。

一个以 Heyting 代数 `H` 为值域的赋值就是从变量到 `H` 的映射。
我们来定义如何对命题公式进行赋值求值。

```lean
variable {H : Type _} [HeytingAlgebra H]
@[simp]
def eval (v : Variable → H) : Formula → H
  | bot    => ⊥
  | # P    => v P
  | A || B => eval v A ⊔ eval v B
  | A && B => eval v A ⊓ eval v B
  | A ⇒ B => eval v A ⇨ eval v B
```

我们说 `A` 是 `Γ` 的一个结果，如果对于任意 Heyting 代数中的赋值，如果对于所有 `B ∈ Γ` ，
  `eval v B` 对于某个元素都是成立的，那么 `eval v A` 对这个元素也是成立的。
  注意，在有限集合 `Γ` 的情况下，这对应于
  `Infimum { eval v B | B ∈ Γ } ≤ eval v A` 。
  这个"与可达版本"的有效性定义在工作中非常方便。

```lean
def Models (Γ : Set Formula) (A : Formula) : Prop :=
  ∀ {H : Type} [HeytingAlgebra H] {v : Variable → H} {c}, (∀ B ∈ Γ, c ≤ eval v B) → c ≤ eval v A

local infix:27 (priority := high) " ⊨ " => Models
def Valid (A : Formula) : Prop := ∅ ⊨ A
```

下面是一些关于有效性的基本性质。

策略 `simp` 将自动化简被标记为 `@[simp]` 的定义，并重写使用标记为 `@[simp]` 的定理。

```lean
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
```

作为一个练习，让我们证明下面这个在直觉逻辑中成立的命题。

```lean
example : Valid (~(A && ~A)) := by {
  -- sorry
  simp [Valid, Models]
  -- sorry
}
```

让我们定义相对于直觉逻辑的可证性。

```lean
section
set_option hygiene false -- 这是一个允许前向引用的恶劣方式
local infix:27 " ⊢ " => ProvableFrom
```

`Γ ⊢ A` 是断言存在一个证明树，其结论为 `A`，假设来自 `Γ`。这是典型的直觉逻辑的自然推理规则列表。

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

为了练习证明系统，让我们证明以下命题。
你可以使用在前面的代码中定义的 `apply_ax` 策略来证明可以使用 `ax` 规则证明的目标。
或者可以手动进行证明，使用有关 `insert` 的以下引理。
```
  mem_insert x s : x ∈ insert x s
  mem_insert_of_mem y : x ∈ s → x ∈ insert y s
```

```lean
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
```

（可选练习）

```lean
example : Provable (~(A && ~A)) := by {
  -- sorry
  apply impI
  exact impE (andE2 (by apply_ax)) (andE1 (by apply_ax))
  -- sorry
}
```

（可选练习）

```lean
example : Provable ((~A && ~B) ⇒ ~(A || B)) := by {
  -- sorry
  apply impI
  apply impI
  apply orE (by apply_ax)
  · exact impE (andE1 (by apply_ax)) (by apply_ax)
  · exact impE (andE2 (by apply_ax)) (by apply_ax)
  -- sorry
}
```

可以使用 `induction` 对 `h` 进行证明。你需要告诉 Lean 你要同时证明所有 `Δ` 的情况，使用 `induction h generalizing Δ`。
如果不显式命名的话，Lean 会将创建的假设标为不可访问（†）。
你可以使用 `rename_i ih` 或 `rename_i A B h ih` 给最后的不可访问变量命名。
或者你可以使用 `case impI ih => <proof>` 来证明特定的情况。
你可能需要使用引理 `insert_subset_insert : s ⊆ t → insert x s ⊆ insert x t`。

```lean
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
```
使用 `apply?` 策略来查找陈述 `Γ ⊆ insert x Γ` 的引理。
你可以点击右侧面板中的蓝色建议来自动应用建议。

```lean
lemma ProvableFrom.insert (h : Γ ⊢ A) : insert B Γ ⊢ A := by {
  -- sorry
  apply weakening h
  -- use `apply?` here
  apply? subset_insert
  -- sorry
}
```

现在证明演绎定理很容易。

```lean
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
  apply? empty_subset
  -- sorry
}
```

这有点棘手，因为你需要使用 Heyting 代数中的运算进行计算。

```lean
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
```
如果你愿意，你现在可以尝试一些更长的项目。

1. 定义 Kripke 语义并证明相对于 Kripke 语义的正确性。

2. 相对于 Heyting 代数语义或 Kripke 语义证明完备性。

```lean
end IntuitionisticPropositionalLogic
```

