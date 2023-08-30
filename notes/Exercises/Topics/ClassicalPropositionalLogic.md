```lean
import GlimpseOfLean.Library.Basic
open Set

namespace ClassicalPropositionalLogic
```

让我们尝试实现经典命题逻辑的语言。

请注意，还有一个适用于直观逻辑的版本：
`IntuitionisticPropositionalLogic.lean`

我们定义了命题公式，并为它们提供了一些符号。

```lean
def Variable : Type := ℕ
```

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

让我们根据估值定义命题的真值，即经典有效性。

```lean
@[simp]
def IsTrue (v : Variable → Prop) : Formula → Prop
  | ⊥      => False
  | # P    => v P
  | A || B => IsTrue v A ∨ IsTrue v B
  | A && B => IsTrue v A ∧ IsTrue v B
  | A ⇒ B => IsTrue v A → IsTrue v B

def Satisfies (v : Variable → Prop) (Γ : Set Formula) : Prop := ∀ {A}, A ∈ Γ → IsTrue v A
def Models (Γ : Set Formula) (A : Formula) : Prop := ∀ {v}, Satisfies v Γ → IsTrue v A
local infix:27 (priority := high) " ⊨ " => Models
def Valid (A : Formula) : Prop := ∅ ⊨ A
```

这是关于有效性的一些基本性质。

策略 `simp` 将自动化简标记为 `@[simp]` 的定义，并进行重写。
使用标记为 `@[simp]` 的定理。

```lean
variable {v : Variable → Prop} {A B : Formula}
@[simp] lemma isTrue_neg : IsTrue v ~A ↔ ¬ IsTrue v A := by simp

@[simp] lemma isTrue_top : IsTrue v ⊤ := by {
  sorry
}

@[simp] lemma isTrue_equiv : IsTrue v (A ⇔ B) ↔ (IsTrue v A ↔ IsTrue v B) := by {
  sorry
}
```

作为练习，让我们证明（使用经典逻辑）双重否定消除原理。
`by_contra h` 可以用于通过矛盾证明某个命题。

```lean
example : Valid (~~A ⇔ A) := by {
  sorry
}

@[simp] lemma satisfies_insert_iff : Satisfies v (insert A Γ) ↔ IsTrue v A ∧ Satisfies v Γ := by {
  simp [Satisfies]
}
```

让我们根据经典逻辑定义可证明性。

```lean
section
set_option hygiene false -- 这是一种允许前向引用的“hacky”方法
local infix:27 " ⊢ " => ProvableFrom
```

`Γ ⊢ A` 是谓词，表示存在一个证明树，其结论为 `A`，假设来自于 `Γ`。
这是用于经典逻辑的典型自然推理规则列表。

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

一个公式是可证明的，如果存在一个证明树：

```lean
def Provable (A : Formula) := ∅ ⊢ A

export ProvableFrom (ax impI impE botC andI andE1 andE2 orI1 orI2 orE)
variable {Γ Δ : Set Formula}
```

我们定义了一个简单的策略 `apply_ax`，用于使用 `ax` 规则证明某个命题。

```lean
syntax "solve_mem" : tactic
syntax "apply_ax" : tactic
macro_rules
  | `(tactic| solve_mem) =>
    `(tactic| first | apply mem_insert | apply mem_insert_of_mem; solve_mem
                    | fail "tactic \'apply_ax\' failed")
  | `(tactic| apply_ax)  => `(tactic| { apply ax; solve_mem })
```

为了熟悉证明系统，让我们证明以下命题。
您可以使用在前面定义的 `apply_ax` 策略，该策略通过 `ax` 规则证明可证明的目标。
或者可以手动完成，使用关于插入的以下引理。
```
  mem_insert x s : x ∈ insert x s
  mem_insert_of_mem y : x ∈ s → x ∈ insert y s
```

```lean
example : insert A (insert B ∅) ⊢ A && B := by
  exact andI (ax (mem_insert _ _)) (ax (mem_insert_of_mem _ (mem_insert _ _)))

example : insert A (insert B ∅) ⊢ A && B := by
  exact andI (by apply_ax) (by apply_ax)

example : Provable (~~A ⇔ A) := by {
  sorry
}
```

可选练习：证明排中律。

```lean
example : Provable (A || ~A) := by {
  sorry
}
```

可选练习：证明德摩根定理之一。
如果要说 `impE` 公理的参数 `A` 应该是 `X && Y`，可以使用 `impE (A := X && Y)`。

```lean
example : Provable (~(A && B) ⇔ ~A || ~B) := by {
  sorry
}
```

您可以使用 `induction` 对 `h` 进行证明。您将希望告诉 Lean 您想要对所有的 `Δ` 进行证明，使用 `induction h generalizing Δ`。
如果您没有显式命名，Lean 将标记所创建的假设为不可访问（标记为†）。
您可以使用 `rename_i ih` 或 `rename_i A B h ih` 为最后一个不可访问的变量命名，或者使用 `case impI ih => <证明>` 证明特定的情况。
您可能需要使用引理 `insert_subset_insert : s ⊆ t → insert x s ⊆ insert x t`。

```lean
lemma weakening (h : Γ ⊢ A) (h2 : Γ ⊆ Δ) : Δ ⊢ A := by {
  sorry
}
```

使用 `apply?` 策略查找以 `Γ ⊆ insert x Γ` 为条件的引理。
您可以点击右侧面板中的蓝色建议自动应用建议。

```lean
lemma ProvableFrom.insert (h : Γ ⊢ A) : insert B Γ ⊢ A := by {
  sorry
}
```

现在很容易证明演绎定理。

```lean
lemma deduction_theorem (h : Γ ⊢ A) : insert (A ⇒ B) Γ ⊢ B := by {
  sorry
}


lemma Provable.mp (h1 : Provable (A ⇒ B)) (h2 : Γ ⊢ A) : Γ ⊢ B := by {
  sorry
}
```

您可以使用 `left` 和 `right` 策略证明析取，如果 `h` 是一个析取，可以使用策略 `cases h` 进行情况分析。

```lean
theorem soundness_theorem (h : Γ ⊢ A) : Γ ⊨ A := by {
  sorry
}

theorem valid_of_provable (h : Provable A) : Valid A := by {
  sorry
}
```

如果您愿意，您可以尝试一下较长的项目。

1. 证明完备性：如果一个公式是有效的，则它是可证明的。
  这是一种可能的证明策略：
  * 如果一个公式是有效的，则它的否定正常形式（NNF）也是有效的；
  * 如果一个公式的NNF是有效的，则它的合取范式（CNF）也是有效的；
  * 如果一个CNF中的公式是有效的，则它在句法上是有效的：
      它的所有子句都包含某个 `A` (或包含 `⊤`) 和 `¬ A`；
  * 如果一个CNF中的公式在句法上是有效的，则它是可证明的；
  * 如果一个公式的CNF是可证明的，则它本身也是可证明的；
  * 如果一个公式的NNF是可证明的，则它本身也是可证明的。

2. 为命题逻辑定义吉恩岑风格的序列演算，并证明它产生相同的可证明性。

```lean
end ClassicalPropositionalLogic
```
