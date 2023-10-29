```lean
import GlimpseOfLean.Library.Basic

open PiNotation
```

# 抽象非理性 101：伽罗瓦伴随

在这个文件中，我们将探讨最简单的伴随之例子：完全格之间的伽罗瓦连接。mathlib中有很多关于这个话题的内容，但在这里，我们将自己动手实践。这个文件构建了这些对象的基础理论，你在那里证明的每一个引理都有名字，并且可以重复使用，以证明下一个引理。

```lean
namespace Tutorial

section InfSup
variable [PartialOrder X]
```

在这一部分，`X` 是一个装备有偏序关系的类型。因此，你可以访问下列引理：
* `le_rfl {a : X} : a ≤ a`
* `le_trans {a b c : X} (h : a ≤ b) (h' : b ≤ c) : a ≤ c`
* `le_antisymm {a b : X} (h : a ≤ b) (h' : b ≤ a) : a = b`

花括号（）中的参数表示这些参数是隐式的，Lean 将从上下文中推断出这些参数。

一个元素 `x₀` 是集合 `s` 在 `X`中的下确界，当且仅当，`X` 中的每一个元素作为 `s` 的下界，都必须小于或等于 `x₀`。

```lean
def isInf (s : Set X) (x₀ : X) :=
  ∀ x, x ∈ lowerBounds s ↔ x ≤ x₀

lemma isInf.lowerBound {s : Set X} {x₀ : X} (h : isInf s x₀) : x₀ ∈ lowerBounds s := by {
  -- sorry
  rw [h]
  -- sorry
}
```

一个集合最多只有一个下确界。

```lean
def isInf.eq {s : Set X} {x₀ x₁ : X} (hx₀ : isInf s x₀) (hx₁ : isInf s x₁) : x₀ = x₁ := by {
  -- sorry
  apply le_antisymm
  · exact (hx₁ _).1 ((hx₀ _).2 le_rfl)
  · exact (hx₀ _).1 ((hx₁ _).2 le_rfl)
  -- sorry
}
```

一个元素 `x₀` 是集合 `s` 在 `X` 中的上确界，当且仅当它低于 `x₀` 的每一个 `X` 的元素都是 `s` 的下界。

```lean
def isSup (s : Set X) (x₀ : X) :=
  ∀ x, x ∈ upperBounds s ↔ x₀ ≤ x
```

下一个引理的证明是通过将 `isInf.lowerBound` 应用于配备了相反顺序关系的 `X` 来完成的。你不需要精确理解如何实现这一点，因为所有使用这个技巧的证明都会提供给你。

```lean
lemma isSup.upperBound {s : Set X} {x₀ : X} (h : isSup s x₀) : x₀ ∈ upperBounds s :=
  isInf.lowerBound (X := OrderDual X) h
```

一个集合最多只有一个上确界。

```lean
lemma isSup.eq {s : Set X} {x₀ x₁ : X} (hx₀ : isSup s x₀) (hx₁ : isSup s x₁) : x₀ = x₁ :=
  isInf.eq (X := OrderDual X) hx₀ hx₁
```

一个从 `Set X` 到 `X` 的函数是一个下确界函数，如果它将每个集合映射到这个集合的下确界。

```lean
def isInfFun (I : Set X → X) :=
  ∀ s : Set X, isInf s (I s)
```

一个从 `集合 X` 到 `X` 的函数是极大值函数，如果它把每个集合映射到该集合的极大值。

```lean
def isSupFun (S : Set X → X) :=
  ∀ s : Set X, isSup s (S s)
```

下个引理是本文件的第一个关键结果。如果 `X` 承认一个
下确界函数，那么它自动承认一个上确界函数。

```lean
lemma isSup_of_isInf {I : Set X → X} (h : isInfFun I) : isSupFun (fun s ↦ I (upperBounds s)) := by {
  -- sorry
  intro s x
  constructor
  · intro hx
    exact (h _).lowerBound hx
  · intros hx y hy
    calc
      y ≤ I (upperBounds s) := (h _ y).mp (fun z hz ↦ hz hy)
      _ ≤ x                 := hx
  -- sorry
}
```

当然，我们也有对偶结果，可以从一个最大函数构建一个下确界函数。

```lean
lemma isInf_of_isSup {S : Set X → X} (h : isSupFun S) : isInfFun (fun s ↦ S (lowerBounds s)) :=
  isSup_of_isInf (X := OrderDual X) h
```

我们现在准备好进行本文件的第一个主要定义：完全格。

Markdown 格式：We are now ready for the first main definition of this file: complete lattices.

完全格是一种配备有偏序、下确界函数和上确界函数的类型。例如，配备有包含顺序、交集函数和并集函数的 `X = Set Y` 就是一个完全格。

```lean
class CompleteLattice (X : Type) [PartialOrder X] where
  I : Set X → X
  I_isInf : isInfFun I
  S : Set X → X
  S_isSup : isSupFun S
```

将完全格 `X` 转化为对偶格。当使用上述的 `OrderDual` 技巧时，Lean 将自动采用此构造方式。

```lean
instance (X : Type) [PartialOrder X] [CompleteLattice X] : CompleteLattice (OrderDual X) where
  I := CompleteLattice.S (X := X)
  I_isInf := CompleteLattice.S_isSup (X := X)
  S := CompleteLattice.I (X := X)
  S_isSup := CompleteLattice.I_isInf (X := X)
```

我们现在可以使用上述的第一个主要结果，从一个部分排序类型的最小值功能或最大值功能构建一个完整的格结构。

从部分有序类型的下确界函数构建完全格构造。

这篇笔记解释如何从给定的部分有序类型 `型` 上的一个下确界函数， 如何构建一个完全格的结构。

## 前提

我们从一个部分有序集开始 `α` ，并给出一个 `α` 上的函数 `inf` ，它对每个 `α` 的集合给出一个元素，这个元素应满足下确界的条件。我们将此函数应用到非空有界集上。

`α` 上的偏序定义了一个二元关系 `≤` ，其具有反身性（每个元素都对自身有序）、反对称性（如果 `a ≤ b` 并且 `b ≤ a` ，那么 `a = b` ）和传递性（如果 `a ≤ b` 并且 `b ≤ c` ，那么 `a ≤ c` ）。

一个元素 `a` 是集合 `s` 的下确界，如果它满足两个条件： 

1. `a` 是 `s` 中所有元素的下界。这就是说，对于所有的 `x ∈ s` ，我们有 `a ≤ x` 。
2. 如果 `b` 是 `s` 的任何下界，那么 `a` 不小于 `b` 。也就是说，如果对于所有的 `x ∈ s` ，我们有 `b ≤ x` ，那么 `a ≤ b` 。

我们的目标是使用 `inf` 函数来构建一个完全格。一个完全格是一个满足以下条件的格：

1. 任意两个元素都有公共下界和公共上界
2. 非空有界子集都有确界和下确界。

## 构造方法

为了实现我们的目标，我们定义了新的上限 `sup` 和完全格结构。

我们可以定义 `sup s` 为所有 `s` 的上界的下确界。由于之前的偏序关系和 `inf` 函数很容易验证：如果一个元素 `a` 是集合中所有元素的上界，那么它就是这些元素的上确界。

结合下确界和上确界，我们可以为 `α` 定义一个完全格结构。我们可以使用 `lean` 的助手函数 `lattice.complete_lattice_of_Inf` 来实现这个构造。

这个构造的正确性依赖于下确界的定义和上确界的存在性。这个定义保证了对于任何集合 `s` ，都存在一个元素 `a` 是 `s` 的下确界。而上确界的存在性确保了任何非空有界的 `s` 都有一个上确界。 结合这两点，可以确保我们可以为 `α` 构建一个完全格的结构。

```lean
def CompleteLattice.mk_of_Inf {I : Set X → X} (h : isInfFun I) : CompleteLattice X where
 I := I
 I_isInf := h
 S := fun s ↦ I (upperBounds s)
 S_isSup := isSup_of_isInf h
```

在部分排序类型上从一个最大上界函数构建一个完全格结构。

Markdown格式：

在部分排序类型上从一个最大上界函数构建一个完全格结构。

```lean
def CompleteLattice.mk_of_Sup {S : Set X → X} (h : isSupFun S) : CompleteLattice X where
 I := fun s ↦ S (lowerBounds s)
 I_isInf := isInf_of_isSup h
 S := S
 S_isSup := h
```

在本节结束之前，`X` 将是一个完全格。

```lean
variable [CompleteLattice X]
```

在一个完全格上的下确界函数。

在一个[完全格](https://zh.wikipedia.org/wiki/%E5%AE%8C%E5%85%A8%E6%A0%BC) (complete lattice) 上，对任意的集合都存在一个下确界 (`infimum`) 和上确界 (`supremum`)。

# 定理

在完全格 L 上，下确界函数 `inf` 实际是一个格同态。

**证明：**

为了证明 `inf` 函数是一个格同态，我们需要展示以下两点：

1. `inf(a, b) = a ∧ b`

2. `inf(a ∨ b) = inf(a) ∨ inf(b)`

对于第一点，由于 a, b 是 L 中的任意元素，a ∧ b 就是 a, b 的下确界，因此 inf(a, b) = a ∧ b。

对于第二点，我们要展示 `inf(a ∨ b) = inf(a) ∨ inf(b)`。为此，我们需要引用到完全格的定义，按照定义，对于任意的子集 S， 如果 S 的所有元素都小于等于某个元素 x，则 x 就是 S 的上确界。

如果 c 是 a ∨ b 的下确界，那么我们有 c ≤ a 和 c ≤ b。因此，c 也是 a, b 的下确界，也就是说 c ≤ inf(a, b)。另一方面，既然 inf(a, b) 是 a 和 b 的下确界，我们有 inf(a, b) ≤ a 和 inf(a, b) ≤ b 。由于 a ∨ b 是 a 和 b 的上确界，我们可以推断出 inf(a, b) ≤ a ∨ b ，也就是 inf(a, b) 是 a ∨ b 的下确界，即 inf(a ∨ b) = inf(a) ∨ inf(b)。

至此，我们证明了在完全格上，下确界函数 `inf` 是一个格同态。

```lean
notation "Inf" => CompleteLattice.I
```

在一个完整的格子上的最大上界函数。

```lean
notation "Sup" => CompleteLattice.S
```

我们现在以完全格言来重新陈述一些上述已证明的引理。

```lean
lemma lowerBound_Inf (s : Set X) : Inf s ∈ lowerBounds s :=
  (CompleteLattice.I_isInf _).lowerBound

lemma upperBound_Sup (s : Set X) : Sup s ∈ upperBounds s :=
  (CompleteLattice.S_isSup _).upperBound
```

我们现在证明一系列的引理，断言 `Inf` （然后通过对偶性 `Sup`）符合你的直觉。如果你觉得你能够证明它们，想看更有趣的东西，你可以随意跳过这些，直接跳到伴随部分。

在下面的第一个引理中，你可能会想使用
`lowerBounds_mono_set ⦃s t : Set α⦄ (hst : s ⊆ t) : lowerBounds t ⊆ lowerBounds s`
或者再次证明它作为你的证明的一部分。

```lean
lemma Inf_subset {s t : Set X} (h : s ⊆ t): Inf t ≤ Inf s := by {
  -- sorry
  apply (CompleteLattice.I_isInf s _).1
  apply lowerBounds_mono_set h
  exact lowerBound_Inf t
  -- sorry
}

lemma Sup_subset {s t : Set X} (h : s ⊆ t): Sup s ≤ Sup t :=
  Inf_subset (X := OrderDual X) h

lemma Inf_pair {x x' : X} : x ≤ x' ↔ Inf {x, x'} = x := by {
  -- sorry
  constructor
  · intro h
    apply (CompleteLattice.I_isInf _).eq
    intro z
    constructor
    · intro hz
      apply hz
      simp
    · intro hz
      simp [hz, hz.trans h]
  · intro h
    rw [← h]
    apply lowerBound_Inf
    simp
  -- sorry
}

lemma Sup_pair {x x' : X} : x ≤ x' ↔ Sup {x, x'} = x' := by {
  rw [Set.pair_comm x x']
  exact Inf_pair (X := OrderDual X)
}

lemma Inf_self_le (x : X) : Inf {x' | x ≤ x'} = x := by {
  -- sorry
  apply (CompleteLattice.I_isInf _).eq
  intro x'
  constructor
  · intro h
    exact h le_rfl
  · intro h x'' hx''
    exact h.trans hx''
  -- sorry
}

lemma Sup_le_self (x : X) : Sup {x' | x' ≤ x} = x :=
  Inf_self_le (X := OrderDual X) x
```

让我们证明 `Set` 构成一个完全格。

---

# **完全格中的`Set`证明**

## **定义**

在秩序理论中，一个集合形成一个 *完全格* ，如果对于该集合中任何子集，该子集的上有界集和下有界集都存在。

## **证明**

我们需要证明对于任何给定的 `Set`，其最小边界（`inf`）和最大边界（`sup`）都存在。

- 对于一个空 `Set` ，最小边界是全体集合（所有的元素），最大边界是空集（没有元素）。

- 对于一个非空 `Set` ，最小边界是 `Set` 中所有元素的交集，最大边界是 `Set` 中所有元素的并集。

因此，以这种方式定义的 `Set` ，它的上下边界始终存在，所以 `Set` 构成一个完全格。

---

请注意，这只是一个证明的简述，实际的数学证明可能需要更详尽和严谨的论述。

```lean
lemma isInfInter {Y : Type} (S : Set (Set Y)) : isInf S (⋂₀ S) := by {
  -- sorry
  intro t
  constructor
  · intro ht x hx u hu
    exact ht hu hx
  · intro ht u hu x hx
    exact ht hx _ hu
  -- sorry
}

lemma isSupUnion {Y : Type} (S : Set (Set Y)) : isSup S (⋃₀ S) := by {
  -- sorry
  intro t
  constructor
  · intro ht x hx
    rcases hx with ⟨s, hs, hx⟩
    exact ht hs hx
  · intro ht u hu x hx
    apply ht
    use u
    tauto
  -- sorry
}

instance {Y : Type} : CompleteLattice (Set Y) where
  I := Set.sInter
  I_isInf := fun S ↦ isInfInter S
  S := Set.sUnion
  S_isSup := fun S ↦ isSupUnion S

end InfSup

section Adjunction
```

我们现在准备好进行这个文件的第二个核心定义：有序类型之间的伴随。

如果在有序类型之间的一对函数 `l` 和 `r` 满足
`∀ x y, l x ≤ y ↔ x ≤ r y`，那么它们就是伴随的。也就是说，它们形成了一个伽罗瓦连接。
其中，`l` 代表 "左"，`r` 代表 "右"。

```lean
def adjunction [PartialOrder X] [PartialOrder Y] (l : X → Y) (r : Y → X) :=
  ∀ x y, l x ≤ y ↔ x ≤ r y
```

你需要记住的例子是直接映射和反向映射之间的伴随。给定 `f : α → β`，我们有：
* `Set.image f : Set α → Set β`，记作 `f ''`
* `Set.preimage f : Set β → Set α`，记作 `f ⁻¹'`

```lean
lemma image_preimage_adjunction {α β : Type} (f : α → β) :
    adjunction (Set.image f) (Set.preimage f) := by {
  intros s t
  exact Set.image_subset_iff
}

lemma adjunction.dual [PartialOrder X] [PartialOrder Y] {l : X → Y} {r : Y → X}
    (h : adjunction l r) :
    adjunction (X := OrderDual Y) (Y := OrderDual X) r l := by {
  -- sorry
  intros y x
  exact (h x y).symm
  -- sorry
}
```

在本节的剩余部分中，`X` 和 `Y` 是完全格。

```lean
variable [PartialOrder X] [CompleteLattice X] [PartialOrder Y] [CompleteLattice Y]
```

我们现在来到本文件的第二个主要定理：完全格的伴随函子定理。这个定理指出，完全格之间的函数只有在与 `Sup`（或者 `Inf`）交换时才是左伴随（或者右伴随）。

我们首先定义候选的右伴随（在不对原始映射做任何假设的情况下）。

构造一个在完全格子间的映射的候选右伴随。
如果映射与 `Sup` 交换，这就是一个实际的伴随，参见 `adjunction_of_Sup` 。

```lean
def mk_right (l : X → Y) : Y → X := fun y ↦ Sup {x | l x ≤ y}
```

以下定理的证明并不长，但也不完全显而易见。
首先你需要理解声明中的符号。`l '' s` 是 `s` 在 `l` 下的直接映射。
这个 `''` 是 `Set.image` 的符号。将你的光标放在这个符号上并使用上下文菜单点击 "跳转到定义"，将会带你到定义 `Set.image` 并包含许多相关引理的文件。在参考解决方案中使用的引理有：

* `Set.image_pair : (f : α → β) (a b : α) : f '' {a, b} = {f a, f b}`
* `Set.image_preimage_subset (f : α → β) (s : Set β) : f '' (f ⁻¹' s) ⊆ s`

证明提示：有一方向很简单并且不使用关键假设。对于另一方向，你可能应该首先证明 `Monotone l`，即 `∀ ⦃a b⦄, a ≤ b → l a ≤ l b`。

```lean
theorem adjunction_of_Sup {l : X → Y} (h : ∀ s : Set X, l (Sup s) = Sup (l '' s)) :
    adjunction l (mk_right l) := by {
  -- sorry
  intro x y
  constructor
  · intro h'
    exact (CompleteLattice.S_isSup {x | l x ≤ y}).upperBound h'
  · intro h'
    have l_mono : Monotone l := by {
      intro a b hab
      have := h {a, b}
      rw [Sup_pair.1 hab, Set.image_pair] at this
      exact Sup_pair.2 this.symm
    }
    calc
      l x ≤ l (mk_right l y) := l_mono h'
      _   = Sup (l '' { x | l x ≤ y }) := h {x | l x ≤ y}
      _   ≤ Sup { y' | y' ≤ y } := Sup_subset (Set.image_preimage_subset l { y' | y' ≤ y })
      _   = y := Sup_le_self y
  -- sorry
}
```

当然，我们也可以以同样的方式构造左伴随。

--------------------
Of course we can also provide a "reverse" constructor, `mk_opposite`.

```lean
def mk_opposite (α : Type*) := α
```

Of notice is the prefix notation, `op`, which you may guess stands for "opposite".

```lean
prefix `op`:max := mk_opposite
```

Now, we can make `op α` an instance of `has_mul` iff `α` has division.

```lean
instance [div : has_div α] : has_mul (op α) :=
{ mul := λ x y, ⟨div x.1 y.1⟩ }
```
We also need to provide an `inv` instance if `α` has multiplication.

```lean
instance [mul : has_mul α] : has_inv (op α) :=
{ inv := λ x, ⟨mul x.1 x.1⟩ }
```
But we can do even better if `α` has both division and multiplication.

```lean
instance [mul_div : has_mul_div α] : has_div_mul (op α) :=
{ ..mul_div.to_has_mul, ..mul_div.to_has_div }
```
Having done that, we also need to define the instances for addition, subtraction and so on.

不仅如此，我们还可以提供一个“反向”构造函数，`mk_opposite`。

```lean
def mk_opposite (α : Type*) := α
```

值得注意的是前缀表示法，`op`，你可能已经猜到，它代表的是“反向”。

```lean
prefix `op`:max := mk_opposite
```

现在，如果 `α` 有除法，我们可以使 `op α` 成为 `has_mul` 的实例。

```lean
instance [div : has_div α] : has_mul (op α) :=
{ mul := λ x y, ⟨div x.1 y.1⟩ }
```
如果 `α` 有乘法，我们还需要提供一个 `inv` 实例。

```lean
instance [mul : has_mul α] : has_inv (op α) :=
{ inv := λ x, ⟨mul x.1 x.1⟩ }
```
但是，如果 `α` 同时有除法和乘法，我们可以做得更好。

```lean
instance [mul_div : has_mul_div α] : has_div_mul (op α) :=
{ ..mul_div.to_has_mul, ..mul_div.to_has_div }
```
做完这些，我们还需要为加法、减法等定义实例。

构建一个完全格之间映射的候选左伴随。
如果该映射与 `Inf` 交换，这就是一个实际的伴随，参见 `adjunction_of_Inf`。

```lean
def mk_left (r : Y → X) : X → Y := fun x ↦ Inf {y | x ≤ r y}

theorem adjunction_of_Inf {r : Y → X} (h : ∀ s : Set Y, r (Inf s) = Inf (r '' s)) :
    adjunction (mk_left r) r :=
  fun x y ↦ (adjunction_of_Sup (X := OrderDual Y) (Y := OrderDual X) h y x).symm

end Adjunction

section Topology
```

在这一部分，我们将把上述发展的理论应用到点集拓扑学上。
我们的首要目标是在给定类型上的拓扑类型 `Topology X` 上赋予一个完全格结构。然后我们把任何映射 `f : X → Y` 变成 `Topology X` 和 `Topology Y` 之间的伴随 `(f⁎, f ^*)`，并用它构建乘积拓扑。当然，数学库知道所有这些，但我们将继续构建我们自己的理论。

```lean
@[ext]
structure Topology (X : Type) where
  isOpen : Set X → Prop
  isOpen_iUnion : ∀ {ι : Type}, ∀ {s : ι → Set X}, (∀ i, isOpen (s i)) → isOpen (⋃ i, s i)
  isOpen_iInter : ∀ {ι : Type}, ∀ {s : ι → Set X}, (∀ i, isOpen (s i)) → Finite ι → isOpen (⋂ i, s i)
```

让我们对我们的定义快速进行两次完整性检查，因为许多教科书在定义拓扑空间时都包含了冗余的条件。

```lean
lemma isOpen_empty (T : Topology X) : T.isOpen ∅ := by {
  have : (∅ : Set X) = ⋃ i : Empty, i.rec
  · rw [Set.iUnion_of_empty]
  rw [this]
  exact T.isOpen_iUnion Empty.rec
}

lemma isOpen_univ (T : Topology X) : T.isOpen Set.univ := by {
  have : (Set.univ : Set X) = ⋂ i : Empty, i.rec
  · rw [Set.iInter_of_empty]
  rw [this]
  exact T.isOpen_iInter  Empty.rec (Finite.of_fintype Empty)
}
```

在 `Topology` 的定义中的 `ext` 属性告诉 Lean 自动构建以下的
延展性引理：
`Topology.ext_iff (T T' : Topology X), T = T' ↔ x.isOpen = y.isOpen`
并且它也为 `ext` 策略注册了这个引理（我们将在下文中回到这个话题）。

我们使用由 `Set (Set X)` 引导的顺序的对偶来排序 `Topology X`。尽管有充分的理由选择这种方式，但它们超出了本教程的范围。

```lean
instance : PartialOrder (Topology X) :=
PartialOrder.lift (β := OrderDual $ Set (Set X)) Topology.isOpen (fun T T' ↦ (Topology.ext_iff T T').2)
```

`拓扑 X` 上的上确界函数。

```lean
def SupTop (s : Set (Topology X)) : Topology X where
  isOpen := fun V ↦ ∀ T ∈ s, T.isOpen V
  isOpen_iUnion := by {
    intros ι t ht a ha
    exact a.isOpen_iUnion fun i ↦ ht i a ha
  }
  isOpen_iInter := by {
    intros ι t ht hι a ha
    exact a.isOpen_iInter (fun i ↦ ht i a ha) hι
}
```

因为上述的 supremum 函数来源于 `OrderDual (Set (Set X))` 的 supremum 函数，它确实是一个 supremum 函数。我们可以陈述一个抽象的引理，但在这里直接证明就很容易，也很有趣。

- `OrderDual (Set (Set X))` 是把 `Set X` 视作偏序集然后取对偶得到的新偏序集，其 supremum 函数是原偏序集的 infimum 函数。
- 一个集合的 supremum 是所有小于等于它的元素集合（闭锁）的最大元素（如果存在的话）。
- 因此，`OrderDual (Set (Set X))` 的 supremum 函数给出了每个集合的下界集合的最大元素，也就是闭锁的最小元素，这符合我们对集合的序基本了解。因此，直接证明该函数是一个 supremum 函数十分直观且有趣。

```lean
lemma isSup_SupTop : isSupFun (SupTop : Set (Topology X) → Topology X) :=
fun _ _ ↦ ⟨fun hT _ hV _ hs ↦ hT hs hV, fun hT T' hT' _ hV ↦ hT hV T' hT'⟩
```

我们可以使用我们的抽象理论来免费获得一个下确界函数，因此在 `Topology X` 上有一个完备格结构。
需要注意的是，我们的抽象理论的确在做非平凡的工作：下确界函数并*不*来自于 `OrderDual (Set (Set X))`。

```lean
instance : CompleteLattice (Topology X) := CompleteLattice.mk_of_Sup isSup_SupTop
```

让我们用完全格记法重新阐述我们对 `Sup` 的构造是什么。这个证明就是简单的说 "这是按定义为真的"。

```lean
lemma isOpen_Sup {s : Set (Topology X)} {V : Set X} : (Sup s).isOpen V ↔ ∀ T ∈ s, T.isOpen V :=
  Iff.rfl
```

我们现在开始通过任意映射 `f : X → Y` 来构建 `Topology X` 和 `Topology Y` 之间的伴随关系。我们会手动构建左伴随，然后调用我们的伴随函子定理。

```lean
def push (f : X → Y) (T : Topology X) : Topology Y where
  isOpen := fun V ↦ T.isOpen (f ⁻¹' V)
  isOpen_iUnion := by {
    -- sorry
    intros ι s hs
    rw [Set.preimage_iUnion]
    exact T.isOpen_iUnion hs
    -- sorry
  }
  isOpen_iInter := by {
    -- sorry
    intros ι s hs hι
    rw [Set.preimage_iInter]
    exact T.isOpen_iInter hs hι
    -- sorry
}

postfix:1024 "⁎" => push -- type using `\_*`
```

一个映射 `f : X → Y` 相对于拓扑 `T` 和 `T'` 是连续的，如果每个开集的原像是开放的。

```lean
def Continuous (T : Topology X) (T' : Topology Y) (f : X → Y) :=  f ⁎ T ≤ T'
```

让我们来确认一下这个定义是否确实表达了我们所声称的内容。

```lean
example (T : Topology X) (T' : Topology Y) (f : X → Y) :
  Continuous T T' f ↔ ∀ V, T'.isOpen V → T.isOpen (f ⁻¹' V) :=
Iff.rfl
```

注意到以下证明使用了 `ext` 策略，这是由于它知道如果两个拓扑具有相同的开集，那么它们就是相等的，这得益于对 `Topology` 定义的 `ext` 属性的应用。

```lean
lemma push_push (f : X → Y) (g : Y →Z) (T : Topology X) :
    g ⁎ (f ⁎ T) = (g ∘ f) ⁎ T := by {
  ext V
  exact Iff.rfl
}
```

我们需要一个与 `f ⁎` 相对应的右伴随，因此我们需要检查它与 `Sup` 是否相交。
你可能想使用
`Set.ball_image_iff : (∀ y ∈ f '' s, p y) ↔ ∀ x ∈ s, p (f x)`
其中 "ball" 代表的是 "bounded for all"，即 `∀ x ∈ ...`。

```lean
lemma push_Sup (f : X → Y) {t : Set (Topology X)} : f ⁎ (Sup t) = Sup (f ⁎ '' t) := by {
  -- sorry
  ext V
  rw [isOpen_Sup, Set.ball_image_iff]
  exact Iff.rfl
  -- sorry
}

def pull (f : X → Y) (T : Topology Y) : Topology X := mk_right (push f) T

postfix:1024 "^*" => pull

def ProductTopology {ι : Type} {X : ι → Type} (T : Π i, Topology (X i)) : Topology (Π i, X i) :=
Inf (Set.range (fun i ↦ (fun x ↦ x i) ^* (T i)))

lemma ContinuousProductTopIff {ι : Type} {X : ι → Type} (T : Π i, Topology (X i))
  {Z : Type} (TZ : Topology Z) {f : Z → Π i, X i}:
    Continuous TZ (ProductTopology T) f ↔ ∀ i,  Continuous TZ (T i) (fun z ↦ f z i) := by {
  -- sorry
  calc
    Continuous TZ (ProductTopology T) f
    _ ↔ f ⁎ TZ ∈ lowerBounds (Set.range (fun i ↦ (fun x ↦ x i) ^* (T i))) := by {
          rw [CompleteLattice.I_isInf]
          exact Iff.rfl
          }
    _ ↔ ∀ i, f ⁎ TZ ≤ (fun x ↦ x i) ^* (T i)        := by rw [lowerBounds_range]
    _ ↔ ∀ i, (fun x ↦ x i) ⁎ (f ⁎ TZ) ≤ T i        := by {
          apply forall_congr'
          intro i
          rw [pull, ← adjunction_of_Sup (fun s ↦ push_Sup _), push_push]
          }
    _ ↔ ∀ i,  Continuous TZ (T i) (fun z ↦ f z i)  := Iff.rfl
```

展开 Continuous ProductTopology
  rw [← CompleteLattice.I_isInf, lowerBounds_range]
  应用 forall_congr'
  引入 i
  展开 pull
  rw [← adjunction_of_Sup (fun s ↦ push_Sup _), push_push]
  rfl

```lean
-- sorry
}

end Topology

namespace Subgroups

@[ext]
structure Subgroup (G : Type) [Group G] where
  carrier : Set G
  one_mem : 1 ∈ carrier
  mul_mem : ∀ ⦃x y : G⦄, x ∈ carrier → y ∈ carrier → x*y ∈ carrier
  inv_mem : ∀ ⦃x : G⦄, x ∈ carrier → x⁻¹ ∈ carrier

instance [Group G] : Membership G (Subgroup G) := ⟨fun x H ↦ x ∈ H.carrier⟩

variable {G : Type} [Group G]

instance : PartialOrder (Subgroup G) :=
  PartialOrder.lift Subgroup.carrier (fun H H' ↦ (Subgroup.ext_iff H H').2)
```

一个群的交集是一个子群。

```lean
def SubgroupInf (s : Set (Subgroup G)) : Subgroup G where
  carrier := ⋂ H ∈ s, H.carrier
  one_mem := by {
    -- sorry
    rw [Set.mem_iInter₂]
    intro H _
    exact H.one_mem
    -- sorry
  }
  mul_mem := by {
    -- sorry
    intro x y hx hy
    rw [Set.mem_iInter₂] at hx hy ⊢
    intro H hH
    exact H.mul_mem (hx H hH) (hy H hH)
    -- sorry
  }
  inv_mem := by {
    -- sorry
    intro x hx
    rw [Set.mem_iInter₂] at hx ⊢
    intro H hH
    exact H.inv_mem (hx H hH)
    -- sorry
  }

lemma SubgroupInf_carrier (s : Set (Subgroup G)) :
  (SubgroupInf s).carrier = ⋂₀ (Subgroup.carrier '' s) :=
by simp [SubgroupInf]
-- omit

lemma isInf.lift [PartialOrder X] {f : Y → X} (hf : Function.Injective f) {s : Set Y} {y : Y}
  (hy : isInf (f '' s) (f y)) : @isInf Y (PartialOrder.lift f hf) s y := by {
  intro y'
  erw [← hy (f y')]
  constructor
  · intro hy' x hx
    rcases hx with ⟨y'', hy'', H⟩
    rw [← H]
    exact hy' hy''
  · intro hy' y'' hy''
    apply hy'
    exact Set.mem_image_of_mem f hy''
}

-- omit
lemma SubgroupInf_is_Inf : isInfFun (SubgroupInf : Set (Subgroup G) → Subgroup G) := by {
  -- sorry
  intro s H
  apply isInf.lift (fun H H' ↦ (Subgroup.ext_iff H H').2)
  rw [SubgroupInf_carrier]
  apply isInfInter
  -- sorry
}

instance : CompleteLattice (Subgroup G) := CompleteLattice.mk_of_Inf SubgroupInf_is_Inf

lemma Inf_carrier (s : Set (Subgroup G)) : (Inf s).carrier = ⋂₀ (Subgroup.carrier '' s) :=
  SubgroupInf_carrier s

def forget (H : Subgroup G) : Set G := H.carrier

def generate : Set G → Subgroup G := mk_left forget

lemma generate_forget_adjunction : adjunction (generate : Set G → Subgroup G) forget := by {
  -- sorry
  exact adjunction_of_Inf SubgroupInf_carrier
  -- sorry
}

variable {G' : Type} [Group G']

def pull (f : G →* G') (H' : Subgroup G') : Subgroup G where
  carrier := f ⁻¹' H'.carrier
  one_mem := by {
    -- sorry
    show f 1 ∈ H'
    rw [f.map_one]
    exact H'.one_mem
    -- sorry
  }
  mul_mem := by {
    -- sorry
    intro x y hx hy
    show f (x*y) ∈ H'
    rw [f.map_mul]
    exact H'.mul_mem hx hy
    -- sorry
  }
  inv_mem := by {
    -- sorry
    intro x hx
    show f x⁻¹ ∈ H'
    rw [f.map_inv]
    exact H'.inv_mem hx
    -- sorry
  }

lemma pull_carrier (f : G →* G') (H' : Subgroup G') : (pull f H').carrier = f ⁻¹' H'.carrier :=
  rfl
```

让我们真正偷懒，通过伴随性定义子群的正向推导。

```lean
def push (f : G →* G') : Subgroup G → Subgroup G' := mk_left (pull f)

lemma push_pull_adjunction (f : G →* G') : adjunction (push f) (pull f) := by {
  -- sorry
  apply adjunction_of_Inf
  intro S
  ext x
  simp [Inf_carrier, Set.image_image, pull, Set.preimage_iInter]
  -- sorry
}

end Subgroups

section
```

我们的下一个具体目标是
`push_generate (f : G →* G') (S : Set G) : push f (generate S) = generate (f '' S)`

这将需要几个更抽象的引理。

```lean
variable {X : Type} [PartialOrder X] [CompleteLattice X]
         {Y : Type} [PartialOrder Y] [CompleteLattice Y]

lemma unique_left {l l' : X → Y} {r : Y → X} (h : adjunction l r) (h' : adjunction l' r) :
    l = l' := by {
  -- sorry
  ext x
  apply le_antisymm
  · rw [h, ← h']
  · rw [h', ← h]
  -- sorry
}

lemma unique_right {l : X → Y} {r r' : Y → X} (h : adjunction l r) (h' : adjunction l r') :
    r = r' := by {
  -- sorry
  exact (unique_left h'.dual h.dual).symm
  -- sorry
}

variable {Z : Type} [PartialOrder Z] [CompleteLattice Z]

lemma adjunction.compose {l : X → Y} {r : Y → X} (h : adjunction l r)
  {l' : Y → Z} {r' : Z → Y} (h' : adjunction l' r') : adjunction (l' ∘ l) (r ∘ r') := by {
  -- sorry
  intro x z
  rw [Function.comp_apply, h', h]
  rfl
  -- sorry
}

-- omit
lemma left_comm_of_right_comm {W : Type} [PartialOrder W] {Z : Type} [PartialOrder Z]
    {lYX : X → Y} {uXY : Y → X} (hXY : adjunction lYX uXY)
    {lWZ : Z → W} {uZW : W → Z} (hZW : adjunction lWZ uZW)
    {lWY : Y → W} {uYW : W → Y} (hWY : adjunction lWY uYW)
    {lZX : X → Z} {uXZ : Z → X} (hXZ : adjunction lZX uXZ)
    (h : uXZ ∘ uZW = uXY ∘ uYW) : lWZ ∘ lZX = lWY ∘ lYX := by {
  have A₁
  · exact hXZ.compose hZW
  rw [h] at A₁
  exact unique_left A₁ (hXY.compose hWY)
}
-- omit

end

namespace Subgroups
variable {G : Type} [Group G] {G' : Type} [Group G']
```

作为最后的挑战，我们提出以下引理。

群态射下，由某些集合 `S` 生成的子群的像，由 `S` 的像生成。

```lean
lemma push_generate (f : G →* G') : push f ∘ generate = generate ∘ (Set.image f) := by {
  -- sorry
  apply left_comm_of_right_comm
  apply image_preimage_adjunction
  apply push_pull_adjunction
  apply generate_forget_adjunction
  apply generate_forget_adjunction
  ext H
  exact Iff.rfl
  -- sorry
}

end Subgroups
end Tutorial
```
