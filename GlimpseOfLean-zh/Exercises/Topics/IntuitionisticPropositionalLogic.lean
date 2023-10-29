

import GlimpseOfLean.Library.Basic
open Set

namespace IntuitionisticPropositionalLogic

/- 让我们试着实现直觉主义命题逻辑的语言。

请注意：此文件也有一个用于经典逻辑的版本：`ClassicalPropositionalLogic.lean`
-/

def Variable : Type := ℕ

/- 我们定义命题公式，并为它们指定一些符号。
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

/- 接下来我们定义 Heyting 代数语义。

在 Heyting 代数 `H` 中的求值，只是从变量到 `H` 的映射
让我们定义如何在命题公式上评估求值。
-/

variable {H : Type _} [HeytingAlgebra H]
@[simp]
def eval (v : Variable → H) : Formula → H
  | bot    => ⊥
  | # P    => v P
  | A || B => eval v A ⊔ eval v B
  | A && B => eval v A ⊓ eval v B
  | A ⇒ B => eval v A ⇨ eval v B

/- 我们说如果对于任何 Heyting 代数的所有取值，如果对所有 `B ∈ Γ` 的 `eval v B` 都高于某一个元素，那么 `eval v A` 就高于这个元素，那么 `A` 就是 `Γ` 的一个结果。注意这对于有限集 `Γ`，完全对应于 `Infimum { eval v B | B ∈ Γ } ≤ eval v A`。这种 "yoneda'd" 版的有效性定义很方便工作使用。
-/

def Models (Γ : Set Formula) (A : Formula) : Prop :=
  ∀ {H : Type} [HeytingAlgebra H] {v : Variable → H} {c}, (∀ B ∈ Γ, c ≤ eval v B) → c ≤ eval v A

local infix:27 (priority := high) " ⊨ " => Models
def Valid (A : Formula) : Prop := ∅ ⊨ A

/- 以下是一些有效性的基本性质。

  使用 `simp` 策略会自动简化被 `@[simp]` 标记的定义，并使用被 `@[simp]` 标记的定理进行重写。
-/

variable {v : Variable → H} {A B : Formula}
@[simp] lemma eval_neg : eval v ~A = (eval v A)ᶜ := by simp

@[simp] lemma eval_top : eval v top = ⊤ := by {
  sorry
}

@[simp]
lemma isTrue_equiv : eval v (A ⇔ B) = (eval v A ⇨ eval v B) ⊓ (eval v B ⇨ eval v A) := by {
  sorry
}

/- 作为一个练习，让我们证明以下命题，该命题符合直觉主义逻辑。

```Lean
Proposition mul_comm (m n : ℕ) : m * n = n * m.
```

首先，我们需要了解在 Lean 中的乘法定义。它是关于自然数的归纳定义，这意味着对于任何自然数 m 和 n ，m * n 根据 n 的归纳定义。特别是，我们有以下两种情况：

```Lean
m * 0     = 0
m * (n+1) = m * n + m
```

接下来，我们将对 n 进行归纳证明。首先，考虑 n = 0 的情况。我们有：

```Lean
m * 0 = 0
0 * m = 0
```

所以对于 n = 0 的情况，命题是正确的。接下来，假设命题对 n 是正确的，那么我们需要证明命题对 n+1 也是正确的。我们有：

```Lean
m * (n+1) = m * n + m
```

我们想要将右边变为 `(n+1) * m` ，我们需要使用归纳 hypotheses 和反对称性质。反对称性质是指对于所有自然数 m, n, p :

```Lean
m + n = m + p → n = p
```

在我们的情况下，我们将应用 `m * n + m = m + n * m`。首先，注意到 由 `+` 的定义右边是可等价的 ：

```Lean
m * n + m = m + n * m
```

然后应用反对称性质，我们有

```Lean
n * m = m * n
```
这是我们的归纳 hypotheses。因此，我们可以得出结论：`m * n + m = (n + 1) * m` 在我们的情况下是正确的。

对所有的 n，我们已经证明了这个等式，这意味着我们证明了 `m * n = n * m`，证明完毕。
-/

example : Valid (~(A && ~A)) := by {
  sorry
}

/- 让我们定义依据直观逻辑的证明性。
-/

section
set_option hygiene false -- this is a hacky way to allow forward reference in notation
local infix:27 " ⊢ " => ProvableFrom

/- `Γ ⊢ A` 是一个断言，表明存在一个结论为 `A` 且其假设来源于 `Γ` 的证明树。 这是对于直观主义逻辑的自然演绎的典型规则表。
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

/- 为了熟练运用该证明系统，让我们来证明以下内容。
  你可以使用之前定义的 `apply_ax` 策略，它可以证明使用 `ax` 规则可以证明的目标。
  或者，你也可以手动使用关于 insert 的以下引理来进行证明。
```
  mem_insert x s : x ∈ insert x s
  mem_insert_of_mem y : x ∈ s → x ∈ insert y s
```
-/

example : Provable ((~A || ~B) ⇒ ~(A && B)) := by {
  sorry
}

/- 可选练习
-/

example : Provable (~(A && ~A)) := by {
  sorry
}

/- 可选练习
-/

example : Provable ((~A && ~B) ⇒ ~(A || B)) := by {
  sorry
}

/- 你可以使用 `归纳法` 在 `h` 上证明以下的定理。你可能会希望告诉 Lean 你想要同时为所有的 `Δ` 进行证明，可以使用 `归纳法 h 概括 Δ` 来实现。
Lean 会把你没有明确命名的假设标记为无法访问的（标记为 †）。
可以使用例如 `rename_i ih` 或 `rename_i A B h ih` 等方式命名后面无法访问的变量。或者你可以通过 `case impI ih => <proof>` 证明某一特定的情况。
你可能需要使用这个引理：`insert_subset_insert : s ⊆ t → insert x s ⊆ insert x t`。
-/

lemma weakening (h : Γ ⊢ A) (h2 : Γ ⊆ Δ) : Δ ⊢ A := by {
  sorry
}

/- 使用 `apply?` 策略来找到表述 `Γ ⊆ insert x Γ` 的引理。
  你可以点击右侧面板的蓝色建议以自动应用建议。
-/

lemma ProvableFrom.insert (h : Γ ⊢ A) : insert B Γ ⊢ A := by {
  sorry
}

/- 证明演绎定理现在很容易了。
-/

lemma deduction_theorem (h : Γ ⊢ A) : insert (A ⇒ B) Γ ⊢ B := by {
  sorry
}

lemma Provable.mp (h1 : Provable (A ⇒ B)) (h2 : Γ ⊢ A) : Γ ⊢ B := by {
  sorry
}

/- 这是复杂的，因为你需要用 Heyting 代数里的运算来计算。
-/

set_option maxHeartbeats 0 in
theorem soundness_theorem (h : Γ ⊢ A) : Γ ⊨ A := by {
  sorry
}

theorem valid_of_provable (h : Provable A) : Valid A := by {
  sorry
}

/- 如果你愿意，你现在可以尝试一些更长的项目。

1. 定义 Kripke 语义并证明其 Kripke 语义的声音性。

2. 证明针对 Heyting 代数语义或 Kripke 语义的完备性。
-/

end IntuitionisticPropositionalLogic

/- 
-/