

import GlimpseOfLean.Library.Basic
open Set

namespace ClassicalPropositionalLogic

/- 让我们尝试实现一个经典命题逻辑的语言。

注意，这个文件也有一个直观逻辑版本：
`IntuitionisticPropositionalLogic.lean`
-/

def Variable : Type := ℕ

/- 我们定义了命题公式，并为它们制定了一些符号表示。
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
local notation (priority := high) "⊥" => bot

def neg (A : Formula) : Formula := A ⇒ ⊥
local notation:(max+2) (priority := high) "~" x:max => neg x
def top : Formula := ~⊥
local notation (priority := high) "⊤" => top
def equiv (A B : Formula) : Formula := (A ⇒ B) && (B ⇒ A)
local infix:29 (priority := high) " ⇔ " => equiv

/- 我们来定义一个相对于估值的真理，即古典有效性。
-/

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

/- 这里是一些关于有效性的基本属性。

策略 `simp` 将自动简化标记为 `@[simp]` 的定义并使用标记为 `@[simp]` 的定理进行重写。
-/

variable {v : Variable → Prop} {A B : Formula}
@[simp] lemma isTrue_neg : IsTrue v ~A ↔ ¬ IsTrue v A := by simp

@[simp] lemma isTrue_top : IsTrue v ⊤ := by {
  -- sorry
  simp
  -- sorry
}

@[simp] lemma isTrue_equiv : IsTrue v (A ⇔ B) ↔ (IsTrue v A ↔ IsTrue v B) := by {
  -- sorry
  simp
  tauto
  -- sorry
}

/- 作为一个练习，让我们证明（使用经典逻辑）双重否定消除原则。
  `by_contra h` 可能对证明悖论有所帮助。
-/

example : Valid (~~A ⇔ A) := by {
  -- sorry
  intros v _
  simp
  tauto
  -- sorry
}

@[simp] lemma satisfies_insert_iff : Satisfies v (insert A Γ) ↔ IsTrue v A ∧ Satisfies v Γ := by {
  simp [Satisfies]
}

/- 我们首先定义经典逻辑下的可证性。
-/

section
set_option hygiene false -- this is a hacky way to allow forward reference in notation
local infix:27 " ⊢ " => ProvableFrom

/- `Γ ⊢ A` 是一个谓词，表示有一个假设来自 `Γ`，结论为 `A` 的证明树。这是经典逻辑中自然推理的典型规则列表。
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
  | botC  : ∀ {Γ A},   insert ~A Γ ⊢ ⊥                → Γ ⊢ A

end

local infix:27 (priority := high) " ⊢ " => ProvableFrom

/- 一种公式被证明是正确的，如果存在一个

```
proof tree
```

证明树

such that

使得

1. The leaves of the proof tree correspond to axioms
2. The internal nodes of the proof tree correspond to inference rules

1. 证明树的叶子对应着公理
2. 证明树的内部节点对应于推理规则

This proof tree can be represented as a mudule where each internal node corresponds to an instance, like `Prop α`, and each leaf corresponds to a definition, like `axioms_1 : Prop α`.

这个证明树可以被表示为一个模块，其中每个内部节点对应一个实例，例如 `Prop α`，每个树叶对应一个定义，比如 `axioms_1 : Prop α`。

```
instance inference_rules_1 : Prop α :=
begin apply axioms_1 end
```

```
实例 inference_rules_1 : Prop α :=
开始 应用 axioms_1 结束
```

Note that the proof tree can be likened to the definition of a programming function: a concise description of a very large and potentially unbounded computation. The computational content of the proof tree, known as the Curry-Howard correspondence, is what makes interactive theorem proving in Lean so powerful.

注意，该证明树可以类比于编程函数的定义：简洁地描述了非常大且可能无界的计算。证明树的计算内容，被称为 Curry-Howard correspondence ，这是使得在 Lean 中的交互式定理证明如此强大的原因。

```
def inference_rules_2 : Prop β → Prop γ :=
begin apply inference_rules_1 end
```

```
定义 inference_rules_2 : Prop β → Prop γ :=
开始 应用 inference_rules_1 结束
```
-/

def Provable (A : Formula) := ∅ ⊢ A

export ProvableFrom (ax impI impE botC andI andE1 andE2 orI1 orI2 orE)
variable {Γ Δ : Set Formula}

/- 我们定义了一个简单的策略 `apply_ax` 来使用 `ax` 规则证明一些东西。
-/

syntax "solve_mem" : tactic
syntax "apply_ax" : tactic
macro_rules
  | `(tactic| solve_mem) =>
    `(tactic| first | apply mem_insert | apply mem_insert_of_mem; solve_mem
                    | fail "tactic \'apply_ax\' failed")
  | `(tactic| apply_ax)  => `(tactic| { apply ax; solve_mem })

/- 为了熟悉证明系统，让我们来证明以下定理。
你可以使用之前定义的 `apply_ax` 策略，可以证明一个可以用 `ax` 规则证明的目标。
或者你可以手动使用关于 insert 的以下引理。
```
  mem_insert x s : x ∈ insert x s
  mem_insert_of_mem y : x ∈ s → x ∈ insert y s
```
-/

example : insert A (insert B ∅) ⊢ A && B := by
  exact andI (ax (mem_insert _ _)) (ax (mem_insert_of_mem _ (mem_insert _ _)))

example : insert A (insert B ∅) ⊢ A && B := by
  exact andI (by apply_ax) (by apply_ax)

example : Provable (~~A ⇔ A) := by {
  -- sorry
  apply andI
  · apply impI
    apply botC
    apply impE _ (by apply_ax)
    apply_ax
  · apply impI
    apply impI
    apply impE (by apply_ax)
    apply_ax
  -- sorry
}

/- 可选练习：证明排除中介的法则。

首先，我们需要在 Lean 中输入的代码：

``` lean
open classical

variables p : Prop

theorem lem : p ∨ ¬p :=
by_cases
  (assume h : p, or.inl h)
  (assume h : ¬p, or.inr h)
```
这段代码在 Lean 中表示 "排除中介的法则" 的证明。现在，让我们将它转化成中文理解。

我们先声明一个逻辑命题 `p`。然后，证明定理 `lem`，即 `p ∨ ¬p`，也就是 "p 或者非 p"，这就是所谓的 "排除中介的法则"。

我们使用 `by_cases` 策略，这是一个基于反证法的策略，允许我们考虑两种可能，一种是 `p` 成立，一种是 `p` 不成立。

- 如果 `p` 成立，那么我们可以使用 `or.inl` 来表示 `p ∨ ¬p` 是因为 `p` 成立而成立。
- 另一种情况，假设 `p` 不成立（即 `¬p`），那么我们可以使用 `or.inr` 来表示 `p ∨ ¬p` 是因为 `¬p` 成立而成立。

上述代码完成了 "排除中介的法则" 的证明。
-/

example : Provable (A || ~A) := by {
  -- sorry
  apply botC
  apply impE (by apply_ax)
  apply orI2
  apply impI
  apply impE (by apply_ax)
  apply orI1 (by apply_ax)
  -- sorry
}

/- 可选练习：证明其中一个德摩根定律。
  如果你希望称 `impE` 公理的参数 `A` 为 `X && Y`，
  你可以使用 `impE (A := X && Y)` 来实现。
-/

example : Provable (~(A && B) ⇔ ~A || ~B) := by {
  -- sorry
  apply andI
  · apply impI
    apply botC
    apply impE (A := A && B) (by apply_ax)
    apply andI
    · apply botC
      apply impE (A := _ || _) (by apply_ax)
      apply orI1 (by apply_ax)
    · apply botC
      apply impE (A := _ || _) (by apply_ax)
      apply orI2 (by apply_ax)
  · apply impI
    apply impI
    apply orE (by apply_ax)
    · apply impE (by apply_ax)
      apply andE1 (by apply_ax)
    · apply impE (by apply_ax)
      apply andE2 (by apply_ax)
  -- sorry
}

/- 你可以使用 `归纳法` 在 `h` 上进行以下证明。你可能需要告诉 Lean，你希望一次性证明所有的 `Δ`，通过使用 `对 h 进行归纳，同时泛化 Δ`。如果你不显式地命名它们，Lean 会将创建的假设标记为无法访问（标记为 †）。您可以使用例如 `rename_i ih` 或 `rename_i A B h ih`来命名最后的不可访问变量。或者你可以使用 `case impI ih => <proof>` 来证明特定的例子。你可能需要使用引理
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
  case botC ih => apply botC; solve_by_elim [insert_subset_insert]
  -- sorry
}

/- 使用 `apply?` 策略来找到声明 `Γ ⊆ insert x Γ` 的引理。
你可以在右边的面板中点击蓝色的建议，以自动应用这个建议。
-/

lemma ProvableFrom.insert (h : Γ ⊢ A) : insert B Γ ⊢ A := by {
  -- sorry
  apply weakening h
  -- use `apply?` here
  exact subset_insert B Γ
  -- sorry
}

/- 证明演绎定理现在变得容易了。
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

/- 你需要使用策略 `left` 和 `right` 来证明一个析取式，并且如果 `h` 是一个析取式，你需要使用策略 `cases h` 来做情冱分析。
-/

theorem soundness_theorem (h : Γ ⊢ A) : Γ ⊨ A := by {
  -- sorry
  induction h <;> intros v hv
  solve_by_elim
  case impI ih => intro hA; apply ih; simp [*]
  case impE ih₁ ih₂ => exact ih₁ hv (ih₂ hv)
  case botC ih => by_contra hA; apply ih (satisfies_insert_iff.mpr ⟨by exact hA, hv⟩)
  case andI ih₁ ih₂ => exact ⟨ih₁ hv, ih₂ hv⟩
  case andE1 ih => exact (ih hv).1
  case andE2 ih => exact (ih hv).2
  case orI1 ih => exact .inl (ih hv)
  case orI2 ih => exact .inr (ih hv)
  case orE ih₁ ih₂ ih₃ => refine (ih₁ hv).elim (fun hA => ih₂ ?_) (fun hB => ih₃ ?_) <;> simp [*]
  -- sorry
}

theorem valid_of_provable (h : Provable A) : Valid A := by {
  -- sorry
  exact soundness_theorem h
  -- sorry
}

/- 如果你愿意，现在可以尝试这些更长的项目。

1. 证明完整性：如果一个公式是有效的，那么它是可证明的
这是这个证明的一种可能策略：
* 如果一个公式是有效的，那么它的否定规范形式（NNF）也是有效的；
* 如果一个处于 NNF 的公式是有效的，那么它的合取范式（CNF）也是有效的；
* 如果一个处于 CNF 的公式是有效的，那么它就是语法上的有效：
  所有的子句都包含 `A` 和 `¬ A`，对某个 `A` 来说（或者包含 `⊤`）；
* 如果一个处于 CNF 的公式在语法上是有效的，那么它是可证明的；
* 如果一个处于 NNF 的公式的 CNF 是可证明的，那么该公式本身也是可证明的；
* 如果一个公式的 NNF 是可证明的，那么该公式本身也是可证明的。

2. 定义 Gentzen's 的顺序演算法，用于命题逻辑，并证明这导致了相同的可证明性。
-/

end ClassicalPropositionalLogic

/- 
-/