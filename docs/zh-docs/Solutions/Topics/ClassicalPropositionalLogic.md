让我们尝试实现一个经典命题逻辑的语言。

请注意，也有适用于直觉逻辑的版本:
`IntuitionisticPropositionalLogic.lean`

我们定义了命题公式，并为它们提供了一些符号表示。

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

让我们根据一个估值定义真值，即经典有效性。

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

这里是一些有效性的基本属性。

`tactic `simp` 会自动简化用`@[simp]`标记的定义，并进行重写操作。
使用标记为`@[simp]`的定理。

```lean
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
```

作为练习，让我们证明（使用经典逻辑）双重否定消除原理。
使用`by_contra h`可以通过矛盾证明某个命题。

```lean
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
```

让我们根据经典逻辑定义可证明性。

```lean
section
set_option hygiene false -- 这是一个让前向引用在符号中可行的权宜之计
local infix:27 " ⊢ " => ProvableFrom
```

`Γ ⊢ A` 是断言，即存在一个具有结论`A`且假设来自`Γ`的证明树。这是一个带有经典逻辑自然推导规则的典型列表。

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

一个公式是可证的，如果有一个

```lean
def Provable (A : Formula) := ∅ ⊢ A

export ProvableFrom (ax impI impE botC andI andE1 andE2 orI1 orI2 orE)
variable {Γ Δ : Set Formula}
```

我们定义了一个简单的策略`tactic `apply_ax`以使用`ax`规则证明一个命题。

```lean
syntax "solve_mem" : tactic
syntax "apply_ax" : tactic
macro_rules
  | `(tactic| solve_mem) =>
    `(tactic| first | apply mem_insert | apply mem_insert_of_mem; solve_mem
                    | fail "tactic \'apply_ax\' failed")
  | `(tactic| apply_ax)  => `(tactic| { apply ax; solve_mem })
```

为了练习证明系统，让我们证明以下命题。
  您可以使用先前定义的`tactic `apply_ax`，它可用于证明可以使用`ax`规则证明的命题。
  或者手动完成，使用下面关于`insert`的引理。
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
```

可选练习：证明排中律。

```lean
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
```

可选练习：证明德摩根定律中的一条。
  如果要说明引理`impE`的参数`A`应该是`X && Y`，可以使用 `impE (A := X && Y)`

```lean
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
```

您可以使用`induction`对`h`进行证明。您可以使用`induction h generalizing Δ`来告诉 Lean 您要为所有的`Δ`同时证明。如果您不显式命名它们，Lean 将标记创建的假设为不可访问（用†标记）。您可以使用`rename_i ih`或`rename_i A B h ih`为最后的不可访问变量命名。或者，您可以使用`case impI ih => <proof>`证明特殊情况。您可能需要使用引理`insert_subset_insert : s ⊆ t → insert x s ⊆ insert x t`。

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
  case botC ih => apply botC; solve_by_elim [insert_subset_insert]
  -- sorry
}
```

使用 `apply?` 策略来查找断言 `Γ ⊆ insert x Γ` 的引理。您可以点击右侧面板中的蓝色建议，以自动使用建议。

```lean
lemma ProvableFrom.insert (h : Γ ⊢ A) : insert B Γ ⊢ A := by {
  -- sorry
  apply weakening h
  -- 在此处使用 `apply?`
  exact subset_insert B Γ
  -- sorry
}
```

现在证明演绎定理很容易了。

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
  -- 这里使用 `apply?` 吧
  exact empty_subset Γ
  -- sorry
}

您可以使用`tactics `left`和`right`来证明一个析取，使用`tactic `cases h`对`h`进行情况分析，如果`h`是一个析取。

```lean
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
```

如果您愿意，现在可以尝试一些较长的项目。

1. 证明完备性：如果一个公式是有效的，则它是可证的。
   这是一个可能的证明策略：
   * 如果一个公式是有效的，则它的否定正常形式（NNF）也是有效的。
   * 如果一个公式的NNF是有效的，则其析取范式（CNF）也是有效的。
   * 如果一个CNF中的公式是有效的，那么它在语法上是有效的：
     所有的子句都包含一个`A`和`¬ A`（或包含一个`⊤`）。
   * 如果一个CNF中的公式在语法上是有效的，那么它是可证的。
   * 如果一个公式的NNF的CNF是可证的，那么这个公式本身也是可证的。
   * 如果一个公式的NNF是可证的，那么这个公式本身也是可证的。

2. 为命题逻辑定义根兹恩的序列演算，并证明它产生相同的可证性。

```lean
end ClassicalPropositionalLogic
```
