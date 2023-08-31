```lean
import GlimpseOfLean.Library.Basic

open PiNotation
```

# 抽象废话 101: Galois 对应

在这个文件中，我们将使用最简单的伴蒙古状态示例：Galois 连接通过完全格。在 mathlib 中有很多关于这个主题的内容，但是在这里我们将为了练习建立我们自己的版本。这个文件构建了这些对象的基本理论，你证明的每个引理都被命名，并且可以被重用来证明下一个引理。

```lean
namespace Tutorial

section InfSup
variable [PartialOrder X]
```

在这个部分中，`X` 是一个配备了偏序关系的类型。所以你可以访问到
依据您提供的内容，我将对其进行翻译：

```lean
import GlimpseOfLean.Library.Basic

open PiNotation

# 抽象的无意义 101: Galois 对应

在这个文件中我们将使用最简单的伴蒙古状态示例：Galois 连接通过完全格。在 mathlib 中有很多关于这个主题的内容，但是在这里我们将为了练习建立我们自己的版本。
这个文件构建了这些对象的基本理论。你证明的每个引理都被命名，并且可以被重用来证明下一个引理。

```lean
namespace Tutorial

section InfSup
variable [PartialOrder X]
```

在这个部分中，`X` 是一个配备了偏序关系的类型。所以你可以访问到

## 引理

- `le_rfl {a : X} : a ≤ a`：对于任意的 `a : X`，有 `a ≤ a`。
- `le_trans {a b c : X} (h : a ≤ b) (h' : b ≤ c) : a ≤ c`：对于任意的 `a b c : X`，如果 `a ≤ b` 且 `b ≤ c`，则有 `a ≤ c`。
- `le_antisymm {a b : X} (h : a ≤ b) (h' : b ≤ a) : a = b`：对于任意的 `a b : X`，如果 `a ≤ b` 且 `b ≤ a`，则有 `a = b`。

在上述引理中，大括号包围的参数表示这些参数是隐式的，Lean 将根据上下文推断这些参数的值。

## 定义

给定集合 `s` 和元素 `x₀`。如果存在一个元素 `x` 满足：当且仅当它小于等于 `x₀` 时，`x` 是 `s` 的下界。

```lean
def isInf (s : Set X) (x₀ : X) :=
  ∀ x, x ∈ lowerBounds s ↔ x ≤ x₀

lemma isInf.lowerBound {s : Set X} {x₀ : X} (h : isInf s x₀) : x₀ ∈ lowerBounds s := by {
  sorry
}
```

一个集合最多只有一个下确界。

```lean
def isInf.eq {s : Set X} {x₀ x₁ : X} (hx₀ : isInf s x₀) (hx₁ : isInf s x₁) : x₀ = x₁ := by {
  sorry
}
```

给定集合 `s` 和元素 `x₀`。如果存在一个元素 `x` 满足：当且仅当它大于等于 `x₀` 时，`x` 是 `s` 的上界。

```lean
def isSup (s : Set X) (x₀ : X) :=
  ∀ x, x ∈ upperBounds s ↔ x₀ ≤ x
```

下一个引理通过将 `X` 配备相反的序关系应用于 `isInf.lowerBound` 而证明。您不需要确切理解这是如何实现的，因为所有使用此技巧的证明都会提供。
```lean
lemma isSup.upperBound {s : Set X} {x₀ : X} (h : isSup s x₀) : x₀ ∈ upperBounds s :=
  isInf.lowerBound (X := OrderDual X) h
```

一个集合最多只有一个上确界。

```lean
lemma isSup.eq {s : Set X} {x₀ x₁ : X} (hx₀ : isSup s x₀) (hx₁ : isSup s x₁) : x₀ = x₁ :=
  isInf.eq (X := OrderDual X) hx₀ hx₁
```

从 `Set X` 到 `X` 的函数是一个下确界函数，如果它将每个集合映射到该集合的下确界。

```lean
def isInfFun (I : Set X → X) :=
  ∀ s : Set X, isInf s (I s)
```

从 `Set X` 到 `X` 的函数是一个上确界函数，如果它将每个集合映射到该集合的上确界。
```
从 `Set X` 到 `X` 的函数是一个上确界函数，如果它将每个集合映射到该集合的上确界。

```lean
def isSupFun (S : Set X → X) :=
  ∀ s : Set X, isSup s (S s)
```

下一个引理是这个文件中的第一个关键结果。如果 `X` 存在一个下确界函数，则它自动存在一个上确界函数。

```lean
lemma isSup_of_isInf {I : Set X → X} (h : isInfFun I) : isSupFun (fun s ↦ I (upperBounds s)) := by {
  sorry
}
```

当然，我们还有由上确界函数构造下确界函数的对偶结果。

```lean
lemma isInf_of_isSup {S : Set X → X} (h : isSupFun S) : isInfFun (fun s ↦ S (lowerBounds s)) :=
  isSup_of_isInf (X := OrderDual X) h
}
```
现在我们准备好对此文件进行第一个主要定义：完备格。

完备格是一种配备了偏序、下确界函数和上确界函数的类型。例如，`X = Set Y` 配备了包含关系的偏序、交集函数和并集函数，就是一个完备格。

```lean
class CompleteLattice (X : Type) [PartialOrder X] where
  I : Set X → X
  I_isInf : isInfFun I
  S : Set X → X
  S_isSup : isSupFun S
```

将完备格 `X` 转换为对偶格。在使用上述的 `OrderDual` 技巧时，Lean 会自动选择这个构造方法。

```lean
instance (X : Type) [PartialOrder X] [CompleteLattice X] : CompleteLattice (OrderDual X) where
  I := CompleteLattice.S (X := X)
  I_isInf := CompleteLattice.S_isSup (X := X)
  S := CompleteLattice.I (X := X)
  S_isSup := CompleteLattice.I_isInf (X := X)
```
现在我们可以使用上面的第一个主要结果，从偏序类型的下确界函数或上确界函数构建一个完备格结构。

从偏序类型的下确界函数构建一个完备格结构。

```lean
def CompleteLattice.mk_of_Inf {I : Set X → X} (h : isInfFun I) : CompleteLattice X where
 I := I
 I_isInf := h
 S := fun s ↦ I (upperBounds s)
 S_isSup := isSup_of_isInf h
```

从偏序类型的上确界函数构建一个完备格结构。

```lean
def CompleteLattice.mk_of_Sup {S : Set X → X} (h : isSupFun S) : CompleteLattice X where
 I := fun s ↦ S (lowerBounds s)
 I_isInf := isInf_of_isSup h
 S := S
 S_isSup := h
```
在这个部分结束之前，`X` 将是一个完备格。

```lean
variable [CompleteLattice X]
```

完备格上的下确界函数。

```lean
notation "Inf" => CompleteLattice.I
```

完备格上的上确界函数。

```lean
notation "Sup" => CompleteLattice.S
```

现在我们将用完备格的术语重新陈述一些上面证明过的引理。

```lean
lemma lowerBound_Inf (s : Set X) : Inf s ∈ lowerBounds s :=
  (CompleteLattice.I_isInf _).lowerBound

lemma upperBound_Sup (s : Set X) : Sup s ∈ upperBounds s :=
  (CompleteLattice.S_isSup _).upperBound
```

现在我们证明一系列引理断言 `Inf`（然后通过对偶性得到的 `Sup`）符合你的直觉。你可以随意跳过它们，跳到下一个部分。
如果你认为自己能够证明这些引理并且想要看到更有趣的内容，你可以跳到下一个关于伴蒙古状态的部分。

在下面的第一个引理中，你可能想要使用 `lowerBounds_mono_set ⦃s t : Set α⦄ (hst : s ⊆ t) : lowerBounds t ⊆ lowerBounds s`，或者在你的证明中重新证明它。

```lean
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
}
```

让我们证明 `Set` 构成一个完备格。

```lean
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
```

现在我们已经准备好进行这个文件的第二个核心定义： ordered types 之间的伴蒙古状态。

如果一对函数 `l` 和 `r` 之间是伴蒙古状态的话，
`∀ x y, l x ≤ y ↔ x ≤ r y`。有时也会说它们构成一个 Galois 对应关系。

```lean
def adjunction [PartialOrder X] [PartialOrder Y] (l : X → Y) (r : Y → X) :=
  ∀ x y, l x ≤ y ↔ x ≤ r y
```

你需要记住的一个例子是直接映射和逆映射之间的伴蒙古状态。给定 `f : α → β`，我们有：
* `Set.image f : Set α → Set β`，表示为 `f ''`
* `Set.preimage f : Set β → Set α`，表示为 `f ⁻¹'`

```lean
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
```
在这个部分的剩余部分，`X` 和 `Y` 是完备格。

```lean
variable [PartialOrder X] [CompleteLattice X] [PartialOrder Y] [CompleteLattice Y]
```

现在我们来到这个文件的第二个主要定理：完备格的伴随函子定理。该定理表明，对于完备格之间的函数，它是左伴随（方向函数，右伴随）当且仅当它与 `Sup`（下确界）（方向函数，`Inf`（上确界））交换。

我们首先定义了候选的右伴随（对原始映射没有任何假设）。

为完备格之间的映射构造一个候选的右伴随。
如果该映射与 `Sup` 交换，那么这将是一个实际的伴随，参见 `adjunction_of_Sup`。

```lean
def mk_right (l : X → Y) : Y → X := fun y ↦ Sup {x | l x ≤ y}
```
以下定理的证明不是很长，但也不完全明显。首先你需要理解陈述中的符号。`l '' s` 是 `s` 在 `l` 下的直接映射。这里的 `''` 是 `Set.image` 的符号。将光标放在这个符号上，然后使用上下文菜单中的 "跳转到定义" 将带你进入定义 `Set.image` 的文件，并包含许多关于它的引理。参考解答中使用的引理有：

* `Set.image_pair : (f : α → β) (a b : α) : f '' {a, b} = {f a, f b}`
* `Set.image_preimage_subset (f : α → β) (s : Set β) : f '' (f ⁻¹' s) ⊆ s`

证明提示：其中一个方向很容易，不需要使用关键的假设。对于另一个方向的证明，需要使用关键假设以及 `f` 与 `Inf` 或 `Sup` 的交换性质。
另一个方向，你应该先证明 `Monotone l`，即 `∀ ⦃a b⦄, a ≤ b → l a ≤ l b`。

```lean
theorem adjunction_of_Sup {l : X → Y} (h : ∀ s : Set X, l (Sup s) = Sup (l '' s)) :
    adjunction l (mk_right l) := by {
  sorry
}
```

当然，我们可以使用相同的方法构建左伴随。

为完备格之间的映射构造一个候选的左伴随。
如果该映射与 `Inf` 交换，那么这将是一个实际的伴随，参见 `adjunction_of_Inf`。

```lean
def mk_left (r : Y → X) : X → Y := fun x ↦ Inf {y | x ≤ r y}

theorem adjunction_of_Inf {r : Y → X} (h : ∀ s : Set Y, r (Inf s) = Inf (r '' s)) :
    adjunction (mk_left r) r :=
  fun x y ↦ (adjunction_of_Sup (X := OrderDual Y) (Y := OrderDual X) h y x).symm

end Adjunction

section Topology
```
在这个部分中，我们将上面发展的理论应用于点集拓扑。我们的第一个目标是给定一个类型 `X` 上的拓扑类型 `Topology X` 赋予一个完备格结构。然后，我们将任何映射 `f: X → Y` 转化为一个 `（f⁎，f ^*）` 之间的伴蒙古状态，其中 `Topology X` 和 `Topology Y`，并使用它来构建乘积拓扑。当然，mathlib 已经知道了这一切，但我们将继续建立自己的理论。

```lean
@[ext]
structure Topology (X : Type) where
  isOpen : Set X → Prop
  isOpen_iUnion : ∀ {ι : Type}, ∀ {s : ι → Set X}, (∀ i, isOpen (s i)) → isOpen (⋃ i, s i)
  isOpen_iInter : ∀ {ι : Type}, ∀ {s : ι → Set X}, (∀ i, isOpen (s i)) → Finite ι → isOpen (⋂ i, s i)
```
让我们对我们的定义进行两个快速的合理性检查，因为很多教科书在拓扑空间的定义中包含了多余的条件。

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

在 `Topology` 定义中的 `ext` 属性告诉 Lean 自动生成以下的外延性引理：
`Topology.ext_iff (T T' : Topology X), T = T' ↔ x.isOpen = y.isOpen` 并且它还使用 `ext` 策略注册了这个引理（我们将在下面回到它）。

我们使用由 `Set (Set X)` 引出的顺序的对偶来对 `Topology X` 进行排序。这种选择有很好的理由，但超出了本教程的范围。

```lean
instance : PartialOrder (Topology X) :=
PartialOrder.lift (β := OrderDual $ Set (Set X)) Topology.isOpen (fun T T' ↦ (Topology.ext_iff T T').2)
```

`Topology X` 上的上确界函数。

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
因为上面的上确界函数来自于 `OrderDual (Set (Set X))` 的上确界函数，所以它实际上是一个上确界函数。我们可以陈述一个抽象引理，但在这里直接证明同样容易且有趣。

```lean
lemma isSup_SupTop : isSupFun (SupTop : Set (Topology X) → Topology X) :=
fun _ _ ↦ ⟨fun hT _ hV _ hs ↦ hT hs hV, fun hT T' hT' _ hV ↦ hT hV T' hT'⟩
```

我们可以利用我们的抽象理论免费得到一个下确界函数，从而得到 `Topology X` 上的完备格结构。
注意，我们的抽象理论确实进行了非平凡的工作：下确界函数 *不是* 来自于 `OrderDual (Set (Set X))`。

```lean
instance : CompleteLattice (Topology X) := CompleteLattice.mk_of_Sup isSup_SupTop
```
让我们用完备格符号重新陈述我们关于 `Sup` 的构造。证明简单地说 "这是根据定义的"。

```lean
lemma isOpen_Sup {s : Set (Topology X)} {V : Set X} : (Sup s).isOpen V ↔ ∀ T ∈ s, T.isOpen V :=
  Iff.rfl
```

我们现在开始构建由任意映射 `f : X → Y` 引起的 `Topology X` 和 `Topology Y` 之间的伴蒙古状态。我们将手工构建左伴随，然后调用我们的伴蒙古函子定理。

```lean
def push (f : X → Y) (T : Topology X) : Topology Y where
  isOpen := fun V ↦ T.isOpen (f ⁻¹' V)
  isOpen_iUnion := by {
    sorry
  }
  isOpen_iInter := by {
    sorry
}

postfix:1024 "⁎" => push -- type using `\_*`
```
关于拓扑 `T` 和 `T'` 的映射 `f: X → Y` 是连续的，如果每个开集的逆映射是开集。

```lean
def Continuous (T : Topology X) (T' : Topology Y) (f : X → Y) :=  f ⁎ T ≤ T'
```

让我们检查一下定义是否确实说的就是我们声称的。

```lean
example (T : Topology X) (T' : Topology Y) (f : X → Y) :
  Continuous T T' f ↔ ∀ V, T'.isOpen V → T.isOpen (f ⁻¹' V) :=
Iff.rfl
```

请注意，下面的证明使用了 `ext` 策略，它知道两个拓扑相等当且仅当它们具有相同的开集，这要归功于 `Topology` 定义中的 `ext` 属性。

```lean
lemma push_push (f : X → Y) (g : Y →Z) (T : Topology X) :
    g ⁎ (f ⁎ T) = (g ∘ f) ⁎ T := by {
  ext V
  exact Iff.rfl
}
```
我们希望 `f ⁎` 有一个右伴随，所以我们需要检查它与 `Sup` 的交换性质。你可能想使用 `Set.ball_image_iff` 引理，其中 "ball" 表示 "bounded for all"，即 `∀ x ∈ ...`。

```lean
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
```
子群的交是一个子群。

```lean
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
}

lemma pull_carrier (f : G →* G') (H' : Subgroup G') : (pull f H').carrier = f ⁻¹' H'.carrier :=
  rfl
```
让我们懒一点，通过伴随定义子群的推前映射。

```lean
def push (f : G →* G') : Subgroup G → Subgroup G' := mk_left (pull f)

lemma push_pull_adjunction (f : G →* G') : adjunction (push f) (pull f) := by {
  sorry
}

end Subgroups

section
```

我们下一个具体的目标是 `push_generate (f : G →* G') (S : Set G) : push f (generate S) = generate (f '' S)`，这将需要几个抽象引理。

```lean
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
```
作为最后的挑战，我们提出以下引理。

群同态的映像在由某个集合 `S` 生成的子群下的作用结果，等于由 `S` 的映像生成的子群。

```lean
lemma push_generate (f : G →* G') : push f ∘ generate = generate ∘ (Set.image f) := by {
  sorry
}

end Subgroups
end Tutorial
```
