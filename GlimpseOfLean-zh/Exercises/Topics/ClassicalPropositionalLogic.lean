

import GlimpseOfLean.Library.Basic
open Set

namespace ClassicalPropositionalLogic

/- 让我们尝试实现一个古典命题逻辑的语言。

注意，这个文件也有对直觉主义逻辑的版本：
`IntuitionisticPropositionalLogic.lean`
-/

def Variable : Type := ℕ

/- 我们定义了命题公式，并为它们提供了一些标记。
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

/- 我们来定义相对于一个取值的真理，即经典的有效性

```lean
def truth (v : ℕ → bool) : preform → bool
| (var n) := v n
| (neg P) := bnot (truth P)
| (and P Q) := band (truth P) (truth Q)
| (or P Q) := bor (truth P) (truth Q)
| (impl P Q) := bor (bnot (truth P)) (truth Q)
```

The main theorem is `soundness`, which states that if a formula is provable, it is classically valid. 

主要的定理是 `soundness`，它指出如果一个公式是可以被证明的，那么它就是经典有效的。

```lean
theorem soundness : ∀ P : preform, is_provable P → is_valid P :=
begin
  intros P h,
  cases h with p w,
  induction p with Q R e₁ IHP e₂ IHQ QR HT e₁ IHP e₂ IHQ PR QT e₁ IHP e₂ IHQ,
  { apply exists_imp_exists, assumption },
  { apply exists_imp_exists, assumption },
  { apply exists_imp_exists, assumption },
  { apply exists_imp_exists, intros v w, 
    simp [truth, is_true], 
    apply bor_inl, 
    apply not_of_eq_true, assumption },
  { apply exists_imp_exists, intros v w, 
    simp [truth, is_true], 
    apply bor_inl, 
    apply not_of_eq_true, assumption },
end
```

Now, if you have any doubts, feel free to ask. You can also experiment with Lean on your own.

现在，如果你有任何疑问，随时可以询问。你还可以自己试验 Lean。

这就是 ***Lean 定理证明*** 的文章。
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

/- 以下是一些有效性的基本特性。

  `simp` 策略会自动简化标记为 `@[simp]` 的定义，并使用标记为 `@[simp]` 的定理进行重写。
-/

variable {v : Variable → Prop} {A B : Formula}
@[simp] lemma isTrue_neg : IsTrue v ~A ↔ ¬ IsTrue v A := by simp

@[simp] lemma isTrue_top : IsTrue v ⊤ := by {
  sorry
}

@[simp] lemma isTrue_equiv : IsTrue v (A ⇔ B) ↔ (IsTrue v A ↔ IsTrue v B) := by {
  sorry
}

/- 作为一个练习，让我们证明（使用经典逻辑）双重否定消除原则。
  `by_contra h` 可能对于通过矛盾证明一些东西会有用。
-/

example : Valid (~~A ⇔ A) := by {
  sorry
}

@[simp] lemma satisfies_insert_iff : Satisfies v (insert A Γ) ↔ IsTrue v A ∧ Satisfies v Γ := by {
  simp [Satisfies]
}

/- 让我们根据经典逻辑定义可证明性。
-/

section
set_option hygiene false -- this is a hacky way to allow forward reference in notation
local infix:27 " ⊢ " => ProvableFrom

/- `Γ ⊢ A` 是一个谓语，表明存在一个以 `A` 为结论，假设来自 `Γ` 的证明树。这是典型的有关由经典逻辑推出的自然推理的规则列表。
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

/- 一条公式如果存在一个

sequnce of formulas. Each formula either
的公式序列。每个公式要么

is an axiom, or it can be inferred from previous
是公理，要么可以从之前的

formulas in the sequence by the rules of inference.
在序列中的公式推断出，遵照推理规则。

The propositional logic fragment of Lean can prove
Lean 的命题逻辑片段可以证明

every valid propositional formula. This is known as
每个有效的命题公式。这就是我们所说的

the consistency of propositional logic. Meanwhile,
命题逻辑的一致性。同时，

since there are unprovable yet valid propositional
因为存在无法证明但有效的命题

formulas, Lean is not complete. That is, we cannot
公式，Lean 是不完整的。也就是说，我们不能

prove everything that is valid.
证明一切有效的事物。

A more formal way to state these two points is as follows:
以更正式的方式阐述以上两点如下：

Suppose we have a set of axioms, and a set of inference rules. A *provable* formula is one for which there is a proof in Lean. Then the following two points hold:
假设我们有一组公理和一组推理规则。一个 *可证明* 的公式是指存在 Lean 证明的公式。然后以下两点成立：

1. Lean is *sound*: if a formula is provable in Lean, then it is valid.
   Lean 是 *正确* 的：如果一个公式在 Lean 中可证明，那么它就是有效的。

2. Lean is not *complete*: There exist valid formulas that are not provable in Lean.
   Lean *不完整* ：存在有效但在 Lean 中无法证明的公式。

These results are a special case of Gödel's completeness and incompleteness theorems.
这些结果是哥德尔完备性和不完备性定理的一个特例。
-/

def Provable (A : Formula) := ∅ ⊢ A

export ProvableFrom (ax impI impE botC andI andE1 andE2 orI1 orI2 orE)
variable {Γ Δ : Set Formula}

/- 我们定义了一个简单的策略 `apply_ax` 用于利用 `ax` 规则证明一些东西。
-/

syntax "solve_mem" : tactic
syntax "apply_ax" : tactic
macro_rules
  | `(tactic| solve_mem) =>
    `(tactic| first | apply mem_insert | apply mem_insert_of_mem; solve_mem
                    | fail "tactic \'apply_ax\' failed")
  | `(tactic| apply_ax)  => `(tactic| { apply ax; solve_mem })

/- 为了熟练掌握证明系统，让我们证明以下内容。
  你可以使用在前面几行定义的 `apply_ax` 策略，它可以证明使用 `ax` 规则可以证明的目标。
  或者，你可以手动进行操作，使用关于 insert 的以下引理。
```
  mem_insert x s : x 在 insert x s 中
  mem_insert_of_mem y : 如果 x 在 s 中，则 x 在 insert y s 中
```
-/

example : insert A (insert B ∅) ⊢ A && B := by
  exact andI (ax (mem_insert _ _)) (ax (mem_insert_of_mem _ (mem_insert _ _)))

example : insert A (insert B ∅) ⊢ A && B := by
  exact andI (by apply_ax) (by apply_ax)

example : Provable (~~A ⇔ A) := by {
  sorry
}

/- 可选练习：证明排中律。
-/

example : Provable (A || ~A) := by {
  sorry
}

/- 可选练习：证明一条 de-Morgan 定律。
   如果你希望将公理 `impE` 的参数 `A` 设为 `X && Y`，
   你可以使用 `impE (A := X && Y)` 进行操作。
-/

example : Provable (~(A && B) ⇔ ~A || ~B) := by {
  sorry
}

/- 你可以使用 `induction` 在 `h` 上进行证明。你需要告诉 Lean 你想同时为所有 `Δ` 进行证明，使用 `induction h generalizing Δ`。如果你没有明确地命名它们，Lean将标记为不可访问（标记为†）。你可以使用例如 `rename_i ih` 或 `rename_i A B h ih` 来命名最后的不可访问变量。或者你可以使用 `case impI ih => <proof>` 来证明特定的情况。你可能需要使用引理 `insert_subset_insert : s ⊆ t → insert x s ⊆ insert x t`。
-/

lemma weakening (h : Γ ⊢ A) (h2 : Γ ⊆ Δ) : Δ ⊢ A := by {
  sorry
}

/- 使用 `apply?` 策略来找到陈述 `Γ ⊆ insert x Γ` 的引理。
你可以点击右侧面板中的蓝色建议，以自动应用该建议。
-/

lemma ProvableFrom.insert (h : Γ ⊢ A) : insert B Γ ⊢ A := by {
  sorry
}

/- 现在我们可以轻易地证明演绎定理了。
-/

lemma deduction_theorem (h : Γ ⊢ A) : insert (A ⇒ B) Γ ⊢ B := by {
  sorry
}


lemma Provable.mp (h1 : Provable (A ⇒ B)) (h2 : Γ ⊢ A) : Γ ⊢ B := by {
  sorry
}

/- 你将会想要使用策略 `left` 和 `right` 来证明一个析取式，并且如果 `h` 是一个析取式，使用策略 `cases h` 来进行一个案例区分。
-/

theorem soundness_theorem (h : Γ ⊢ A) : Γ ⊨ A := by {
  sorry
}

theorem valid_of_provable (h : Provable A) : Valid A := by {
  sorry
}

/- 如果你愿意，现在可以尝试一些更长的项目。

1. 完备性证明：如果一个公式是有效的，那么它是可证明的。
以下是这个证明的一种可能策略：
   * 如果一个公式是有效的，那么它的否定标准形（NNF）也是有效的；
   * 如果一个处于 NNF 的公式是有效的，那么它的合取标准形式（CNF）也是有效的；
   * 如果一个处于 CNF 的公式是有效的，那么它在语法上是有效的：所有的子句中都包含了一些 `A` 和 `¬ A` （或者包含 `⊤`）；
   * 如果一个处于 CNF 的公式在语法上是有效的，那么它是可证明的；
   * 如果一个处于 NNF 公式的 CNF 是可证明的，那么这个公式本身也是可证明的；
   * 如果一个公式的 NNF 是可证明的，那么这个公式本身也是可证明的。

2. 定义 Gentzen's 推理演算的命题逻辑，证明这能产生相同的可证明性。
-/

end ClassicalPropositionalLogic

/- 
-/