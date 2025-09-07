```lean
import GlimpseOfLean.Library.Basic
open Set

namespace ClassicalPropositionalLogic

```

让我们尝试实现一种经典命题逻辑语言。

注意这里还有用于直觉主义逻辑的版本：
`IntuitionisticPropositionalLogic.lean`

```lean
def Variable : Type := ℕ

```

我们定义命题公式和一些符号。

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
local notation (priority := high) "⊥" => bot

def neg (A : Formula) : Formula := A ⇒ ⊥
local notation:(max+2) (priority := high) "~" x:max => neg x
def top : Formula := ~⊥
local notation (priority := high) "⊤" => top
def equiv (A B : Formula) : Formula := (A ⇒ B) && (B ⇒ A)
local infix:29 (priority := high) " ⇔ " => equiv

```

让我们定义相对于赋值的真值，即经典有效性

```lean
@[simp]
def IsTrue (φ : Variable → Prop) : Formula → Prop
  | ⊥      => False
  | # P    => φ P
  | A || B => IsTrue φ A ∨ IsTrue φ B
  | A && B => IsTrue φ A ∧ IsTrue φ B
  | A ⇒ B => IsTrue φ A → IsTrue φ B

def Satisfies (φ : Variable → Prop) (Γ : Set Formula) : Prop := ∀ {A}, A ∈ Γ → IsTrue φ A
def Models (Γ : Set Formula) (A : Formula) : Prop := ∀ {φ}, Satisfies φ Γ → IsTrue φ A
local infix:27 (priority := high) " ⊨ " => Models
def Valid (A : Formula) : Prop := ∅ ⊨ A

```

以下是有效性的一些基本性质。

  策略 `simp` 会自动简化用 `@[simp]` 标记的定义，并使用
用 `@[simp]` 标记的定理进行重写。

```lean
variable {φ : Variable → Prop} {A B : Formula}
@[simp] lemma isTrue_neg : IsTrue φ ~A ↔ ¬ IsTrue φ A := by simp [neg]

@[simp] lemma isTrue_top : IsTrue φ ⊤ := by
  sorry

@[simp] lemma isTrue_equiv : IsTrue φ (A ⇔ B) ↔ (IsTrue φ A ↔ IsTrue φ B) := by
  sorry

```

作为练习，让我们使用（经典逻辑）证明双重否定消除原理。
`by_contra h` 可能对反证法证明有用。

```lean
example : Valid (~~A ⇔ A) := by
  sorry

```

我们经常需要向集合中添加元素。这通过 `insert` 函数完成：
`insert A Γ` 表示 `Γ ∪ {A}`。

```lean
@[simp] lemma satisfies_insert_iff : Satisfies φ (insert A Γ) ↔ IsTrue φ A ∧ Satisfies φ Γ := by
  simp [Satisfies]

```

让我们定义相对于经典逻辑的可证性。

```lean
section
set_option hygiene false -- 这是允许记号中前向引用的技巧性方法
local infix:27 " ⊢ " => ProvableFrom

```

`Γ ⊢ A` 是存在一个结论为 `A` 且假设来自 `Γ` 的证明树的谓词。
这是经典逻辑自然演绎的典型规则列表。

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
  | botC  : ∀ {Γ A},   insert ~A Γ ⊢ ⊥                → Γ ⊢ A

end

local infix:27 (priority := high) " ⊢ " => ProvableFrom

```

如果公式可以从空假设集合中证明，则称该公式是可证的。

```lean
def Provable (A : Formula) := ∅ ⊢ A

export ProvableFrom (ax impI impE botC andI andE1 andE2 orI1 orI2 orE)
variable {Γ Δ : Set Formula}

```

我们定义一个简单的策略 `apply_ax` 来使用 `ax` 规则证明某些东西。

```lean
syntax "solve_mem" : tactic
syntax "apply_ax" : tactic
macro_rules
  | `(tactic| solve_mem) =>
    `(tactic| first | apply mem_singleton | apply mem_insert |
                      apply mem_insert_of_mem; solve_mem
                    | fail "tactic \'apply_ax\' failed")
  | `(tactic| apply_ax)  => `(tactic| { apply ax; solve_mem })

```

要熟悉证明系统，让我们证明以下内容。
  你可以使用前几行定义的 `apply_ax` 策略，它证明使用 `ax` 规则可证的目标。
  或者你可以手动完成，使用以下关于 insert 的引理。
```
  mem_singleton x : x ∈ {x}
  mem_insert x s : x ∈ insert x s
  mem_insert_of_mem y : x ∈ s → x ∈ insert y s
```

```lean
-- Let’s first see an example using the `apply_ax` tactic
example : {A, B} ⊢ A && B := by
  apply andI
  apply_ax
  apply_ax

-- 同样的内容，一次性手动完成。
example : {A, B} ⊢ A && B := by
  exact andI (ax (mem_insert _ _)) (ax (mem_insert_of_mem _ (mem_singleton _)))


example : Provable (~~A ⇔ A) := by
  sorry

```

可选练习：证明排中律。

```lean
example : Provable (A || ~A) := by
  sorry

```

可选练习：证明德摩根定律之一。
  如果你想说公理 `impE` 的参数 `A` 应该是 `X && Y`，
你可以使用 `impE (A := X && Y)` 来做到这一点

```lean
example : Provable (~(A && B) ⇔ ~A || ~B) := by
  sorry

```

你可以使用对 `h` 的 `induction` 来证明以下内容。你需要告诉 Lean 你想使用 `induction h generalizing Δ` 同时对所有 `Δ` 证明它。Lean 会将创建的假设标记为不可访问的（用 † 标记），如果你没有明确地命名它们。
你可以使用例如 `rename_i ih` 或 `rename_i A B h ih` 来命名最后的不可访问变量。或者你可以使用 `case impI ih => <proof>` 证明特定情况。你可能需要使用引理 `insert_subset_insert : s ⊆ t → insert x s ⊆ insert x t`。

```lean
lemma weakening (h : Γ ⊢ A) (h2 : Γ ⊆ Δ) : Δ ⊢ A := by
  sorry

```

使用 `apply?` 策略找到陈述 `Γ ⊆ insert x Γ` 的引理。你可以点击右侧面板中的蓝色建议来自动应用建议。

```lean
lemma ProvableFrom.insert (h : Γ ⊢ A) : insert B Γ ⊢ A := by
  sorry

```

现在证明演绎定理很容易。

```lean
lemma deduction_theorem (h : Γ ⊢ A) : insert (A ⇒ B) Γ ⊢ B := by
  sorry

lemma Provable.mp (h1 : Provable (A ⇒ B)) (h2 : Γ ⊢ A) : Γ ⊢ B := by
  sorry

```

- 你需要使用策略 `left` 和 `right` 来证明析取，并且使用
策略 `cases h`（如果 `h` 是析取）来进行情况区分。

```lean
theorem soundness_theorem (h : Γ ⊢ A) : Γ ⊨ A := by
  sorry

theorem valid_of_provable (h : Provable A) : Valid A := by
  sorry

```

  如果你愿意，你现在可以尝试一些这些较长的项目。

  1. 证明完备性：如果一个公式是有效的，那么它是可证的
  以下是此证明的一种可能策略：
  * 如果一个公式是有效的，那么它的否定范式 (NNF) 也是有效的；
  * 如果 NNF 中的公式是有效的，那么它的合取范式 (CNF) 也是有效的；
  * 如果 CNF 中的公式是有效的，那么它在语法上是有效的：
      它的所有子句都包含某个 `A` 的 `A` 和 `¬ A`（或包含 `⊤`）；
  * 如果 CNF 中的公式在语法上是有效的，那么它是可证的；
  * 如果 NNF 中公式的 CNF 是可证的，那么公式本身也是可证的。
  * 如果公式的 NNF 是可证的，那么公式本身也是可证的。

  2. 为命题逻辑定义 Gentzen 的序列演算，并证明这产生了
  相同的可证性。

```lean
end ClassicalPropositionalLogic


```