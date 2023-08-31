```lean
import GlimpseOfLean.Library.Basic
open Set

namespace IntuitionisticPropositionalLogic
```

让我们试着实现直觉命题逻辑的语言。

注意，这个文件还有一个经典逻辑版本：`ClassicalPropositionalLogic.lean`

```lean
def Variable : Type := ℕ
```

我们定义命题公式，并为它们添加一些符号表示法。

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

在 Heyting 代数 `H` 中的赋值只是从变量到 `H` 的映射。
让我们定义如何对命题公式进行赋值求值。

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

我们说 `A` 是 `Γ` 的结果，如果对于任何 Heyting 代数中的赋值，如果所有 `B ∈ Γ` 都有 `eval v B` 大于某个元素，则 `eval v A` 大于此元素。
注意，对于有限集合 `Γ`，这正好对应于 `Infimum { eval v B | B ∈ Γ } ≤ eval v A`。
这种“洋纳达”版本的有效性定义非常方便处理。

```lean
def Models (Γ : Set Formula) (A : Formula) : Prop :=
  ∀ {H : Type} [HeytingAlgebra H] {v : Variable → H} {c}, (∀ B ∈ Γ, c ≤ eval v B) → c ≤ eval v A

local infix:27 (priority := high) " ⊨ " => Models
def Valid (A : Formula) : Prop := ∅ ⊨ A
```

下面是一些关于有效性的基本性质。

策略 `simp` 会自动简化带有 `@[simp]` 标记的定义，并使用带有 `@[simp]` 标记的定理进行重写。

```lean
variable {v : Variable → H} {A B : Formula}
@[simp] lemma eval_neg : eval v ~A = (eval v A)ᶜ := by simp

@[simp] lemma eval_top : eval v top = ⊤ := by {
  sorry
}

@[simp]
lemma isTrue_equiv : eval v (A ⇔ B) = (eval v A ⇨ eval v B) ⊓ (eval v B ⇨ eval v A) := by {
  sorry
}
```

作为一个练习，我们来证明在直觉逻辑中成立的以下命题。

```lean
example : Valid (~(A && ~A)) := by {
  sorry
}
```

让我们根据直觉逻辑定义可证性。

```lean
section
set_option hygiene false -- 这是一种不太正规的方式，允许在记法中引用前向引用
local infix:27 " ⊢ " => ProvableFrom
```

`Γ ⊢ A` 是谓词，表示存在一个带有前提来自 `Γ` 的证明树，其结论为 `A`。这是一组直观逻辑中自然推理的典型规则列表。

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

为了练习证明系统，让我们来证明下面的命题。
你可以使用前面定义的 `apply_ax` 策略，它用于证明可以使用 `ax` 规则证明的目标。
或者你可以手动证明，使用关于 `insert` 的以下引理。
```
  mem_insert x s : x ∈ insert x s
  mem_insert_of_mem y : x ∈ s → x ∈ insert y s
```

```lean
example : Provable ((~A || ~B) ⇒ ~(A && B)) := by {
  sorry
}
```

可选练习

```lean
example : Provable (~(A && ~A)) := by {
  sorry
}
```

可选练习

```lean
example : Provable ((~A && ~B) ⇒ ~(A || B)) := by {
  sorry
}
```

你可以使用对 `h` 进行归纳证明以下命题。你需要告诉 Lean，你希望同时对所有 `Δ` 进行证明，使用 `induction h generalizing Δ`。如果你不显式命名它们，Lean 将把创建的假设标记为 "inaccessible"（用 † 标记）。你可以使用 `rename_i ih` 或 `rename_i A B h ih` 为最后一个不可访问变量命名。或者你可以使用 `case impI ih => <证明>` 来证明特定的情况。你可能需要使用以下引理：
```
insert_subset_insert : s ⊆ t → insert x s ⊆ insert x t
```

```lean
lemma weakening (h : Γ ⊢ A) (h2 : Γ ⊆ Δ) : Δ ⊢ A := by {
  sorry
}
```

使用 `apply?` 策略找到语句 `Γ ⊆ insert x Γ` 的引理。您可以点击右侧面板中的蓝色建议来自动应用该建议。

```lean
lemma ProvableFrom.insert (h : Γ ⊢ A) : insert B Γ ⊢ A := by {
  sorry
}
```

现在证明演绎定理很容易。

```lean
lemma deduction_theorem (h : Γ ⊢ A) : insert (A ⇒ B) Γ ⊢ B := by {
  sorry
}

lemma Provable.mp (h1 : Provable (A ⇒ B)) (h2 : Γ ⊢ A) : Γ ⊢ B := by {
  sorry
}
```

由于需要在 Heyting 代数中进行运算，这有些棘手。

```lean
set_option maxHeartbeats 0 in
theorem soundness_theorem (h : Γ ⊢ A) : Γ ⊨ A := by {
  sorry
}

theorem valid_of_provable (h : Provable A) : Valid A := by {
  sorry
}
```

如果你愿意，你现在可以尝试一些更长的项目。
1. 首先，我们需要定义 Kripke 语义。在 Lean 中定义 Kripke 模型时，我们需要定义 Kripke 模型的三个部分：状态集合、顺序关系（反映部分关系）和评估函数。

在这里，我们使用自然数表示状态集合，`le` 来表示顺序关系。评估函数将语言中的命题公式映射到每个状态上的真值。

```lean
structure KripkeModel {H : Type} :=
  (States : Type)
  (Rel : States → States → Prop)
  (Val : States → Formula → H)

variable {H : Type} [HeytingAlgebra H]

def evalK {H : Type} [HeytingAlgebra H] {M : KripkeModel} (s : M.States) (v : Variable → M.States) : M.States → Formula → H
  | s bot    => ⊥
  | s (# P)  => (v P).Val s
  | s (A || B) => evalK s v A ⊔ evalK s v B
  | s (A && B) => evalK s v A ⊓ evalK s v B
  | s (A ⇒ B) => evalK s v A ⇨ evalK s v B

def ValidK (A : Formula) : Prop := ∀ {H : Type} [HeytingAlgebra H] {M : KripkeModel}, (∀ (s : M.States) (v : Variable → M.States), evalK s v M.States A = ⊤)
```

接下来，我们需要证明声音性（soundness）的定理，即证明如果 `A` 的模型论（Kripke 语义）为 `⊤`，则 `A` 是可证的。

```lean
theorem soundnessK (A : Formula) : ValidK A → Provable A := by {
  sorry
}
```

2. 关于完全性的证明取决于你选择使用的语义（Heyting 代数语义或 Kripke 语义）。

- 如果你选择使用 Heyting 代数语义，你可以证明 Heyting 代数语义是完全的，即如果 `A` 是有效的，则 `A` 可证。
- 如果你选择使用 Kripke 语义，你可以证明 Kripke 语义是完全的，即如果 `A` 是有效的，则 `A` 在 Kripke 模型中的所有状态上成立。

我将这部分留给你来完成。你可以在完成后结束命令。

```lean
end IntuitionisticPropositionalLogic
```
