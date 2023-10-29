

import GlimpseOfLean.Library.Basic

open PiNotation

/- # 抽象无意义 101：Galois 伴随

在这个文件中，我们将尝试最简单的伴随示例：完全格之间的 Galois 连接。尽管在 mathlib 中有很多关于这个主题的内容，但是在这里，我们会创建自己的版本进行练习。这篇文件构建了这些对象的基础理论，每个你在其中证明的引理都有名字，可以用来证明下一个引理。
-/

namespace Tutorial

section InfSup
variable [PartialOrder X]

/- 在本节中，`X` 是一个配备了偏序关系的类型。所以你可以访问以下引理：
* `le_rfl {a : X} : a ≤ a` 
* `le_trans {a b c : X} (h : a ≤ b) (h' : b ≤ c) : a ≤ c` 
* `le_antisymm {a b : X} (h : a ≤ b) (h' : b ≤ a) : a = b` 

大括号围绕的参数意味着这些参数是隐式的，Lean 将从上下文中推断出这些参数。
-/

/- 一个元素 `x₀` 是集合 `s` 在 `X` 中的下确界，当且仅当 `X` 中的每个元素都是 `s` 的下界，并且它们都小于 `x₀`。
-/

def isInf (s : Set X) (x₀ : X) :=
  ∀ x, x ∈ lowerBounds s ↔ x ≤ x₀

lemma isInf.lowerBound {s : Set X} {x₀ : X} (h : isInf s x₀) : x₀ ∈ lowerBounds s := by {
  sorry
}

/- 一个集合最多只有一个下确界。
-/

def isInf.eq {s : Set X} {x₀ x₁ : X} (hx₀ : isInf s x₀) (hx₁ : isInf s x₁) : x₀ = x₁ := by {
  sorry
}

/- 一个元素 `x₀` 是集合 `s` 在 `X` 中的上确界，当且仅当 `X` 中的每个元素都是 `s` 的下界，并且它们都小于 `x₀`。
-/

def isSup (s : Set X) (x₀ : X) :=
  ∀ x, x ∈ upperBounds s ↔ x₀ ≤ x

/- 下一条引理的证明是通过将 `isInf.lowerBound` 应用于配备了
相反的顺序关系的 `X` 来完成的。你不需要精确地理解这是如何
实现的，因为使用这个技巧的所有证明都将会提供。


-/

lemma isSup.upperBound {s : Set X} {x₀ : X} (h : isSup s x₀) : x₀ ∈ upperBounds s :=
  isInf.lowerBound (X := OrderDual X) h

/- 一个集合最多有一个上确界。
-/

lemma isSup.eq {s : Set X} {x₀ x₁ : X} (hx₀ : isSup s x₀) (hx₁ : isSup s x₁) : x₀ = x₁ :=
  isInf.eq (X := OrderDual X) hx₀ hx₁

/- 如果一个函数从 `Set X` 到 `X` ，并且它将每个集合映射到该集合的下确界，那么这个函数就被称为下确界函数。
-/

def isInfFun (I : Set X → X) :=
  ∀ s : Set X, isInf s (I s)

/- 一个从 `Set X` 到 `X` 的函数是一个 supremum 函数，如果它将每一个集合都映射到这个集合的 supremum。
-/

def isSupFun (S : Set X → X) :=
  ∀ s : Set X, isSup s (S s)

/- 下面的引理是这个文件中的第一个关键结果。如果 `X` 有一个下确界函数，那么它自动会有一个上确界函数。
-/

lemma isSup_of_isInf {I : Set X → X} (h : isInfFun I) : isSupFun (fun s ↦ I (upperBounds s)) := by {
  sorry
}

/- 当然，我们也有一种双重结果，可以从一个取最大值的功能中构造出一个取最小值的功能。
-/

lemma isInf_of_isSup {S : Set X → X} (h : isSupFun S) : isInfFun (fun s ↦ S (lowerBounds s)) :=
  isSup_of_isInf (X := OrderDual X) h

/- 我们现在准备好了这个文件的第一个主要定义：完全格。

---

Markdown 格式请保持，特殊格式前后带空格。
-/

/- 一个完全格是一种装备了偏序关系、最小值函数和最大值函数的类型。例如，用包含顺序、交集函数和并集函数装备的 `X = Set Y` 是一个完全格。
-/

class CompleteLattice (X : Type) [PartialOrder X] where
  I : Set X → X
  I_isInf : isInfFun I
  S : Set X → X
  S_isSup : isSupFun S

/- 将完全格 `X` 转换为对偶格。当使用上述的 `OrderDual` 技巧时， Lean 会自动采用这种构造。

注：`完全格`、`对偶格`和`OrderDual`都是数学上的专业术语。
-/

instance (X : Type) [PartialOrder X] [CompleteLattice X] : CompleteLattice (OrderDual X) where
  I := CompleteLattice.S (X := X)
  I_isInf := CompleteLattice.S_isSup (X := X)
  S := CompleteLattice.I (X := X)
  S_isSup := CompleteLattice.I_isInf (X := X)

/- 我们现在可以使用上述的第一个主要结果，基于一个部分有序类型上的下确界或上确界函数，来构建一个完全格。


-/

/- 从部分有序类型的下确界函数构建一个完全格结构。

---
本文描述了如何使用 Lean 定理证明器，通过下确界函数来构建在部分有序类型上的完全格结构。

我们从部分有序类型 *(Partially Ordered Type)* 开始，这是一个集合类型 `Type`，集合的元素具有反身性、传递性和反对称性。有一些操作符 `≤` 表示“小于或等于”，满足以下条件：
- 反身性：对于所有的 `x`，`x ≤ x`；
- 传递性：如果 `x ≤ y` 并且 `y ≤ z`，那么 `x ≤ z`；
- 反对称性：如果 `x ≤ y` 并且 `y ≤ x`，那么 `x = y`。

接下来，我们定义一个 [`inf`](https://leanprover.github.io/) 函数，它接收两个参数并返回一个结果，这个结果是参数集合的 *下确界* （也称为 *最小界* 或 *下界* ）。

我们的目标是从 `inf` 函数出发，构建一个 *完全格* 结构。完全格是一个格结构，其中任何集合都有一个上确界和下确界。这意味着，我们需要定义两个函数 `Sup` 和 `Inf`，分别代表上确界和下确界。

Lean 定理证明的主要目标之一就是确保构建的完全格结构满足一些基本属性，如：
- 如果 `x ≤ Sup S` 对于集合 `S` 中的所有 `x` 都成立，那么 `Sup S` 是 `S` 的上确界；
- 如果 `Inf S ≤ x` 对于集合 `S` 中的所有 `x` 都成立，那么 `Inf S` 是 `S` 的下确界；

我们还需要证明一些其他属性，以确保 `Sup` 和 `Inf` 函数的行为与我们期望的行为一致。通过证明这些属性，我们可以确信我们的完全格结构是有效的，并且可以用于进一步的数理逻辑研究。
-/

def CompleteLattice.mk_of_Inf {I : Set X → X} (h : isInfFun I) : CompleteLattice X where
 I := I
 I_isInf := h
 S := fun s ↦ I (upperBounds s)
 S_isSup := isSup_of_isInf h

/- 从部分排序类型的上确界函数建立完全格构造。

## 定理声明

我们考虑一个部分排序类型 `P` ，并且给定一个函数 `Sup : set P -> P`，这个函数满足以下性质：

* 对于任何集合`s`， `Sup s`是`s`的一个上界。
* 对于任何集合`s`和任何`x`， 如果 `x`是`s`的上界，那么`Sup s <= x`。

我们希望从这个 `Sup` 函数构造一个完全格`complete lattice`。

一种完全格应满足以下性质：

* 它是一个部分排序集。
* 对于每个集合，该集合的最小元素和最大元素存在（即完全格上的上确界和下确界函数是存在的）。

## 证明

我们需要证明如果 `Sup` 函数满足声明中的性质，则可以从 `Sup` 函数建立一个完全格。 

我们可以构造 `Inf`函数（下确界函数）如下：对于一个集合`s`， `Inf s`被定义为`Sup {b | ∀a∈s, b <= a}`。这就是说，`Inf s`是所有`s`中的元素的下界的集合的上确界。

首先，我们可以证明，对于任何集合`s`，`Inf s`确实是`s`的一个下界：假设有一个`a`属于`s`，由`Inf`的定义，对于`b`属于 `{b | ∀a∈s, b <= a}`，我们有`b <= a`。因此，`Sup {b | ∀a∈s, b <= a}`（即`Inf s`）满足`Inf s <= a`，这意味着`Inf s`是`s`的一个下界。

然后，我们可以证明，对于任何`s`的下界`x`，我们有 `x <= Inf s`：因为 `x` 是 `s` 的一个下界，故 `x` 属于 `{b | ∀a∈s, b <= a}`。那么，由于 `Sup {b | ∀a∈s, b <= a}`（即`Inf s`）是 `{b | ∀a∈s, b <= a}` 的一个上界，我们可以得出 `x <= Inf s`。

因此，我们证明了，对于任何集合`s`，下确界函数 `Inf s`都是存在的，这就证明了我们可以从 `Sup` 函数构造一个完全格。
-/

def CompleteLattice.mk_of_Sup {S : Set X → X} (h : isSupFun S) : CompleteLattice X where
 I := fun s ↦ S (lowerBounds s)
 I_isInf := isInf_of_isSup h
 S := S
 S_isSup := h

/- 在本节的结尾之前，`X` 将是一个完全格。
-/

variable [CompleteLattice X]

/- 在一个完备格上的下确界函数。
-/

notation "Inf" => CompleteLattice.I

/- 一个完全格子上的上确界函数。
-/

notation "Sup" => CompleteLattice.S

/- 我们现在用完全格的术语重新陈述一些已经证明过的引理。
-/

lemma lowerBound_Inf (s : Set X) : Inf s ∈ lowerBounds s :=
  (CompleteLattice.I_isInf _).lowerBound

lemma upperBound_Sup (s : Set X) : Sup s ∈ upperBounds s :=
  (CompleteLattice.S_isSup _).upperBound

/- 我们现在证明一系列引理，这些引理表明 `Inf` （然后通过对偶性 `Sup` ）
的行为符合你的直觉。如果你觉得你能够证明它们并且你想看到更有趣的东西，你可以随意跳过这些并跳到伴随部分。

在下面的第一个引理中，你可能会想使用
`lowerBounds_mono_set ⦃s t : Set α⦄ (hst : s ⊆ t) : lowerBounds t ⊆ lowerBounds s`
或者在你的证明中重新证明它。
-/

lemma Inf_subset {s t : Set X} (h : s ⊆ t): Inf t ≤ Inf s := by {
  sorry
}

lemma Sup_subset {s t : Set X} (h : s ⊆ t): Sup s ≤ Sup t :=
  Inf_subset (X := OrderDual X) h

lemma Inf_pair {x x' : X} : x ≤ x' ↔ Inf {x, x'} = x := by {
  sorry
}

lemma Sup_pair {x x' : X} : x ≤ x' ↔ Sup {x, x'} = x' := by {
  rw [Set.pair_comm x x']
  exact Inf_pair (X := OrderDual X)
}

lemma Inf_self_le (x : X) : Inf {x' | x ≤ x'} = x := by {
  sorry
}

lemma Sup_le_self (x : X) : Sup {x' | x' ≤ x} = x :=
  Inf_self_le (X := OrderDual X) x

/- 让我们证明 `Set` 构成了一个完全格。

A *lattice* is a set `L` of elements that is ordered that, for any two elements `x` and `y` in `L`, the two elements have a unique *supremum* (also called the least upper bound) and a unique *infimum* (also called the greatest lower bound). In the `Set` we know as Boolean algebra, the supremum is the `union` of two sets and the infimum is their `intersection`.

一个*格*是一个元素集合 `L` ，该集合的元素排列有序，对于 `L` 中的任何两个元素 `x` 和 `y` ，存在一个唯一的*上确界*（也称为最小上界）和一个唯一的*下确界*（也称为最大下界）。在我们所知的作为布尔代数的 `Set` 中，上确界是两个集合的 `并集` ，下确界是它们的 `交集`。

A *complete* lattice is a lattice that, additionally, has a least element `0` and a greatest element `1`, and that every *subset* of `L` has a supremum and an infimum. In other words, this means that `Set` is *closed* under finite intersections and finite unions, and that every subset of `Set` has a supremum and an infimum.

一个*完全*格是一个格，它具有最小元素 `0` 和最大元素 `1` ，并且 `L` 的每个*子集*都有上确界和下确界。换句话说，这意味着 `Set` *封闭*于有限交集和有限并集，并且 `Set` 的每个子集都有上确界和下确界。

Let's suppose the contrary, that is, there exists a subset `A` of `Set` such that `A` does not have a supremum or an infimum in `Set`. If `A` does not have a supremum in `Set` then there exists at least one element `b` of `Set` such that `b` is strictly greater than all elements of `A`. If `A` does not have an infimum in `Set`, then there exists at least one element `a` of `Set` such that `a` is strictly less than all elements of `A`.

让我们假设相反的情况，也就是存在一个 `Set` 的子集 `A` ，使得 `A` 在 `Set` 中没有上确界或下确界。如果 `A` 在 `Set` 中没有上确界，那么至少存在一个 `Set` 的元素 `b` ，使得 `b` 严格大于 `A` 的所有元素。如果 `A` 在 `Set` 中没有下确界，那么至少存在一个 `Set` 的元素 `a` ，使得 `a` 严格小于 `A` 的所有元素。

This contradicts the property of `Set` being a complete lattice. Therefore, `Set` forms a complete lattice.

这与 `Set` 是一个完全格的属性相矛盾。因此， `Set` 构成了一个完全格。
-/

lemma isInfInter {Y : Type} (S : Set (Set Y)) : isInf S (⋂₀ S) := by {
  sorry
}

lemma isSupUnion {Y : Type} (S : Set (Set Y)) : isSup S (⋃₀ S) := by {
  sorry
}

instance {Y : Type} : CompleteLattice (Set Y) where
  I := Set.sInter
  I_isInf := fun S ↦ isInfInter S
  S := Set.sUnion
  S_isSup := fun S ↦ isSupUnion S

end InfSup

section Adjunction

/- 我们现在准备好了这个文件的第二个核心定义：有序类型之间的伴随。

这个特别的定义允许我们通过导出两种类型之间的 `Galois` 连接来处理 *量词* 。这它可以将 `∀` 和 `∃` 理解为一个有序集合上的类型构造器。这使我们可以以完全一样的方式处理它们，从而克服了他们在传统逻辑中的根本区别。

**定义**
一个 `Galois` 连接 `(lower : β → α, upper : α → β)` 满足以下性质：

1. `mono (map lower upper)`：输入相同的 `upper` 返回的结果也相同。
2. `strict_mono (map upper lower)`：输入相同的 `lower` 返回的结果也相同。
3. `∀ a : α, b : β, (upper a ≤ b) ↔ (a ≤ lower b)`：关于一个给定的有序对，我们定义 `a` 是 `b` 的上边界。

**例子**
考虑有序集 `{x ℝ // 0 ≤ x} `和 `{y ℝ // 0 < y}` 之间的 `Galois` 连接。我们可以定义 `lower : {y ℝ // 0 < y} → {x ℝ // 0 ≤ x}` 为 `λ y, max 0 y` ，以及 `upper : {x ℝ // 0 ≤ x} → {y ℝ // 0 < y}` 为 `λ x, if 0 < x then x else 1` 。这种定义满足上述三个性质，显然就构成了一个 `Galois` 连接。
-/

/- 如果一对有序类型之间的函数 `l` 和 `r` 满足
`∀ x y, l x ≤ y ↔ x ≤ r y`，则它们是伴随的。
我们也可以说它们形成了一个 Galois 连接。
这里的 `l` 代表 "左"，`r` 代表 "右"。
-/

def adjunction [PartialOrder X] [PartialOrder Y] (l : X → Y) (r : Y → X) :=
  ∀ x y, l x ≤ y ↔ x ≤ r y

/- 你需要记住的例子是直接映像和反向映像之间的伴随关系。给定 `f : α → β`，我们有：
* `Set.image f : Set α → Set β`，用 `f ''` 表示
* `Set.preimage f : Set β → Set α`，用 `f ⁻¹'` 表示
-/

lemma image_preimage_adjunction {α β : Type} (f : α → β) :
    adjunction (Set.image f) (Set.preimage f) := by {
  intros s t
  exact Set.image_subset_iff
}

lemma adjunction.dual [PartialOrder X] [PartialOrder Y] {l : X → Y} {r : Y → X}
    (h : adjunction l r) :
    adjunction (X := OrderDual Y) (Y := OrderDual X) r l := by {
  sorry
}

/- 在本节的剩余部分中，`X` 和 `Y` 是完备格。
-/

variable [PartialOrder X] [CompleteLattice X] [PartialOrder Y] [CompleteLattice Y]

/- 我们现在来到这个文件的第二个主要定理：完全格子的伴随函子定理。此定理说的是，如果一个在完全格子间的函数与 `Sup`（或与 `Inf`）对换，则该函数是左伴随（或右伴随）。

我们首先定义候选的右伴随（在不做任何关于原始映射的假设的情况下）。
-/

/- 构造了一个完整格之间的映射的候选右伴随映射。
如果这个映射与 `Sup` 相交换，那么这就是一个真正的伴随，见 `adjunction_of_Sup` 。
-/

def mk_right (l : X → Y) : Y → X := fun y ↦ Sup {x | l x ≤ y}

/- 以下定理的证明并不长，但也并非显而易见。
首先，你需要理解声明中的记号。 `l '' s` 是 `l` 下的 `s` 的直接映像。
此 `''` 是 `Set.image` 的记号。将光标放在此记号上并使用上下文菜单"跳转到定义"将带你到定义 `Set.image` 并包含许多关于它的引理的文件。在参考解决方案中使用的是

* `Set.image_pair : (f : α → β) (a b : α) : f '' {a, b} = {f a, f b}`
* `Set.image_preimage_subset (f : α → β) (s : Set β) : f '' (f ⁻¹' s) ⊆ s`

证明提示：有一个方向很简单，不需要使用关键的假设。对于另一个方向，你可能应该首先证明 `Monotone l`，即
`∀ ⦃a b⦄, a ≤ b → l a ≤ l b`。
-/

theorem adjunction_of_Sup {l : X → Y} (h : ∀ s : Set X, l (Sup s) = Sup (l '' s)) :
    adjunction l (mk_right l) := by {
  sorry
}

/- 当然，我们也可以采用相同的方法来构造左伴随。
-/

/- 构造了一个完全格之间映射的候选左伴随。 
如果映射与 `Inf` 交换，则这是一个实际的伴随，参见 `adjunction_of_Inf`。
-/

def mk_left (r : Y → X) : X → Y := fun x ↦ Inf {y | x ≤ r y}

theorem adjunction_of_Inf {r : Y → X} (h : ∀ s : Set Y, r (Inf s) = Inf (r '' s)) :
    adjunction (mk_left r) r :=
  fun x y ↦ (adjunction_of_Sup (X := OrderDual Y) (Y := OrderDual X) h y x).symm

end Adjunction

section Topology

/- 在这一节中，我们将应用上述开发的理论到点集拓扑学。
我们首先的目标是为给定类型的拓扑 `Topology X` 赋予一个完全格子结构。然后我们把任何映射 `f : X → Y` 转化为 `Topology X` 和 `Topology Y` 之间的伴随 `(f⁎, f ^*)`，并使用它来构建乘积拓扑。当然，mathlib 已知道了所有这些，但我们将继续构建我们自己的理论。
-/

@[ext]
structure Topology (X : Type) where
  isOpen : Set X → Prop
  isOpen_iUnion : ∀ {ι : Type}, ∀ {s : ι → Set X}, (∀ i, isOpen (s i)) → isOpen (⋃ i, s i)
  isOpen_iInter : ∀ {ι : Type}, ∀ {s : ι → Set X}, (∀ i, isOpen (s i)) → Finite ι → isOpen (⋂ i, s i)

/- 让我们对我们的定义进行两个快速的健全性检查，因为许多教科书在定义拓扑空间时都包含了冗余的条件。
-/

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

/- `ext` 属性在 `Topology` 的定义中告诉 Lean 自动构建以下的扩展性引理：
`Topology.ext_iff (T T' : Topology X), T = T' ↔ x.isOpen = y.isOpen`
并且它还会将此引理注册供 `ext` 策略使用（我们稍后会再谈到这个）。
-/

/- 我们根据 `Set (Set X)` 引发的顺序对 `Topology X` 进行逆序排列。这样选择的原因是有利的，但这超出了本教程的范围。
-/

instance : PartialOrder (Topology X) :=
PartialOrder.lift (β := OrderDual $ Set (Set X)) Topology.isOpen (fun T T' ↦ (Topology.ext_iff T T').2)

/- `Topology X`上的上确界函数。
-/

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

/- 因为以上的 supremum 函数来源于 `OrderDual (Set (Set X))` 的 supremum 函数，它确实是一个至上函数。我们可以陈述一个抽象的引理来证明这一点，但是在这里，直接证明同样简单且非常有趣。
-/

lemma isSup_SupTop : isSupFun (SupTop : Set (Topology X) → Topology X) :=
fun _ _ ↦ ⟨fun hT _ hV _ hs ↦ hT hs hV, fun hT T' hT' _ hV ↦ hT hV T' hT'⟩

/- 我们可以使用我们的抽象理论免费获取一个下确界函数，因此在 `Topology X` 上生成一个完全格结构。
请注意，我们的抽象理论确实在做非平凡的工作：下确界函数并*不*来自 `OrderDual (Set (Set X))`。
-/

instance : CompleteLattice (Topology X) := CompleteLattice.mk_of_Sup isSup_SupTop

/- 让我们用完全格表示法重述我们对 `Sup` 的构建。这个证明只是在说 "这是定义决定的真理"。
-/

lemma isOpen_Sup {s : Set (Topology X)} {V : Set X} : (Sup s).isOpen V ↔ ∀ T ∈ s, T.isOpen V :=
  Iff.rfl

/- 我们现在开始构建由任意映射 `f : X → Y` 引导的 `Topology X` 和 `Topology Y` 之间的伴随。我们将手动构建左伴随，然后调用我们的伴随函子定理。
-/

def push (f : X → Y) (T : Topology X) : Topology Y where
  isOpen := fun V ↦ T.isOpen (f ⁻¹' V)
  isOpen_iUnion := by {
    sorry
  }
  isOpen_iInter := by {
    sorry
}

postfix:1024 "⁎" => push -- type using `\_*`

/- 如果对于所有开放集，其预映像都是开放的，那么映射 `f : X → Y` 就是相对于拓扑结构 `T` 和 `T'` 连续的。
-/

def Continuous (T : Topology X) (T' : Topology Y) (f : X → Y) :=  f ⁎ T ≤ T'

/- 让我们来验证这个定义确实如我们所声称的那样。

``` lean
theorem add_left_cancel : ∀ (a b c : ℕ), 
  a + b = a + c → b = c :=
begin
  intros a b c,
  revert b c,
  induction' a with d hd,  
  -- Base case
  { intros b c h,
    exact h },
  -- Inductive step
  { intros b c h,
    apply hd,
    apply nat.succ.inj,
    exact h }
end
```
在这个定理中，我们声明了对所有的 `a, b, c ∈ ℕ` ，如果 `a + b = a + c` ，那么 `b = c`。首先，我们介绍了 `a, b, c`，然后退回到 `b, c` 。对 `a` 进行归纳，对于基本情况，我们简单地使用假设 `h` ，而对于归纳步骤，我们应用了归纳假设 `hd` 和“自然数注入”，即 `nat.succ.inj` ，并使用假设 `h`。
-/

example (T : Topology X) (T' : Topology Y) (f : X → Y) :
  Continuous T T' f ↔ ∀ V, T'.isOpen V → T.isOpen (f ⁻¹' V) :=
Iff.rfl

/- 注意下面的证明如何使用 `ext` 策略，由于在 `Topology` 的定义上有 `ext` 属性，它知道两个拓扑是相等的当且仅当它们有相同的开集。
-/

lemma push_push (f : X → Y) (g : Y →Z) (T : Topology X) :
    g ⁎ (f ⁎ T) = (g ∘ f) ⁎ T := by {
  ext V
  exact Iff.rfl
}

/- 我们想要一个与 `f ⁎` 的右伴随，所以我们需要检查它是否与`Sup`交换。
你可能需要使用 
`Set.ball_image_iff : (∀ y ∈ f '' s, p y) ↔ ∀ x ∈ s, p (f x)`
其中 "ball" 代表 "bounded for all"，即 `∀ x ∈ ...`。
-/

lemma push_Sup (f : X → Y) {t : Set (Topology X)} : f ⁎ (Sup t) = Sup (f ⁎ '' t) := by {
  sorry
}

def pull (f : X → Y) (T : Topology Y) : Topology X := mk_right (push f) T

postfix:1024 "^*" => pull

def ProductTopology {ι : Type} {X : ι → Type} (T : Π i, Topology (X i)) : Topology (Π i, X i) :=
Inf (Set.range (fun i ↦ (fun x ↦ x i) ^* (T i)))

lemma ContinuousProductTopIff {ι : Type} {X : ι → Type} (T : Π i, Topology (X i))
  {Z : Type} (TZ : Topology Z) {f : Z → Π i, X i}:
    Continuous TZ (ProductTopology T) f ↔ ∀ i,  Continuous TZ (T i) (fun z ↦ f z i) := by {
  sorry
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

/- 一个群的交集是一个子群。
-/

def SubgroupInf (s : Set (Subgroup G)) : Subgroup G where
  carrier := ⋂ H ∈ s, H.carrier
  one_mem := by {
    sorry
  }
  mul_mem := by {
    sorry
  }
  inv_mem := by {
    sorry
  }

lemma SubgroupInf_carrier (s : Set (Subgroup G)) :
  (SubgroupInf s).carrier = ⋂₀ (Subgroup.carrier '' s) :=
by simp [SubgroupInf]

lemma SubgroupInf_is_Inf : isInfFun (SubgroupInf : Set (Subgroup G) → Subgroup G) := by {
  sorry
}

instance : CompleteLattice (Subgroup G) := CompleteLattice.mk_of_Inf SubgroupInf_is_Inf

lemma Inf_carrier (s : Set (Subgroup G)) : (Inf s).carrier = ⋂₀ (Subgroup.carrier '' s) :=
  SubgroupInf_carrier s

def forget (H : Subgroup G) : Set G := H.carrier

def generate : Set G → Subgroup G := mk_left forget

lemma generate_forget_adjunction : adjunction (generate : Set G → Subgroup G) forget := by {
  sorry
}

variable {G' : Type} [Group G']

def pull (f : G →* G') (H' : Subgroup G') : Subgroup G where
  carrier := f ⁻¹' H'.carrier
  one_mem := by {
    sorry
  }
  mul_mem := by {
    sorry
  }
  inv_mem := by {
    sorry
  }

lemma pull_carrier (f : G →* G') (H' : Subgroup G') : (pull f H').carrier = f ⁻¹' H'.carrier :=
  rfl

/- 我们来偷懒一些，通过伴随性定义子群的前推。

-/

def push (f : G →* G') : Subgroup G → Subgroup G' := mk_left (pull f)

lemma push_pull_adjunction (f : G →* G') : adjunction (push f) (pull f) := by {
  sorry
}

end Subgroups

section

/- 我们的下一个具体目标是
`push_generate (f : G →* G') (S : Set G) : push f (generate S) = generate (f '' S)`

这将需要一些更抽象的引理。
-/

variable {X : Type} [PartialOrder X] [CompleteLattice X]
         {Y : Type} [PartialOrder Y] [CompleteLattice Y]

lemma unique_left {l l' : X → Y} {r : Y → X} (h : adjunction l r) (h' : adjunction l' r) :
    l = l' := by {
  sorry
}

lemma unique_right {l : X → Y} {r r' : Y → X} (h : adjunction l r) (h' : adjunction l r') :
    r = r' := by {
  sorry
}

variable {Z : Type} [PartialOrder Z] [CompleteLattice Z]

lemma adjunction.compose {l : X → Y} {r : Y → X} (h : adjunction l r)
  {l' : Y → Z} {r' : Z → Y} (h' : adjunction l' r') : adjunction (l' ∘ l) (r ∘ r') := by {
  sorry
}



end

namespace Subgroups
variable {G : Type} [Group G] {G' : Type} [Group G']

/- 作为最后的挑战，我们提出以下引理。
-/

/- 一个群态射下的一些集合 `S` 生成的子群的像，由 `S` 的像生成。
-/

lemma push_generate (f : G →* G') : push f ∘ generate = generate ∘ (Set.image f) := by {
  sorry
}

end Subgroups
end Tutorial

/- 
-/