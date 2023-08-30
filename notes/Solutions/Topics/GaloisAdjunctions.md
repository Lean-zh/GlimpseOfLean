```lean
import GlimpseOfLean.Library.Basic

open PiNotation
```

# 抽象废话 101: Galois 对应

在这个文件中，我们将尝试处理最简单的 adjunctions 示例：complete lattices 之间的 Galois 联系。
在 mathlib 中有很多关于这个主题的内容，但是在这里我们将亲自来实现一个版本以供练习。这个文件构建了这些对象的基本理论，
你证明的每个引理都有一个命名，可以被重用来证明下一个引理。

```lean
namespace Tutorial

section InfSup
variable [PartialOrder X]
```

在这个部分中，`X` 是一个带有偏序关系的类型。因此你可以访问到
* `le_rfl {a : X} : a ≤ a`
* `le_trans {a b c : X} (h : a ≤ b) (h' : b ≤ c) : a ≤ c`
* `le_antisymm {a b : X} (h : a ≤ b) (h' : b ≤ a) : a = b`

花括号表示这些参数是隐式参数，Lean 会从上下文中推断出这些参数的值。

如果集合 `s` 在 `X` 中拥有一个下确界 `x₀`，那么 `x₀` 是 `s` 的每个元素的下界当且仅当它小于等于 `x₀`。

```lean
def isInf (s : Set X) (x₀ : X) :=
  ∀ x, x ∈ lowerBounds s ↔ x ≤ x₀

lemma isInf.lowerBound {s : Set X} {x₀ : X} (h : isInf s x₀) : x₀ ∈ lowerBounds s := by {
  -- sorry
  rw [h]
  -- sorry
}
```
一个集合最多有一个下确界。

```lean
def isInf.eq {s : Set X} {x₀ x₁ : X} (hx₀ : isInf s x₀) (hx₁ : isInf s x₁) : x₀ = x₁ := by {
  -- sorry
  apply le_antisymm
  · exact (hx₁ _).1 ((hx₀ _).2 le_rfl)
  · exact (hx₀ _).1 ((hx₁ _).2 le_rfl)
  -- sorry
}
```

如果集合 `s` 在 `X` 中拥有一个上确界 `x₀`，那么 `x₀` 是 `s` 的每个元素的上界当且仅当它大于等于 `x₀`。

```lean
def isSup (s : Set X) (x₀ : X) :=
  ∀ x, x ∈ upperBounds s ↔ x₀ ≤ x
```

下一个引理通过将 `isInf.lowerBound` 应用到带有相反序关系的 `X` 上来进行证明。你不需要精确理解这是如何实现的，因为所有使用这个技巧的证明都会呈现给你。

```lean
lemma isSup.upperBound {s : Set X} {x₀ : X} (h : isSup s x₀) : x₀ ∈ upperBounds s :=
  isInf.lowerBound (X := OrderDual X) h
```

一个集合最多有一个上确界。

```lean
lemma isSup.eq {s : Set X} {x₀ x₁ : X} (hx₀ : isSup s x₀) (hx₁ : isSup s x₁) : x₀ = x₁ :=
  isInf.eq (X := OrderDual X) hx₀ hx₁
```

从 `Set X` 到 `X` 的函数是一个下确界函数，如果它将每个集合映射到它们的下确界。
对于这个集合，如果 `X` 存在一个下确界函数，那么它自动也存在一个上确界函数。

```lean
def isSup_of_isInf {I : Set X → X} (h : isInfFun I) : isSupFun (fun s ↦ I (upperBounds s)) := by {
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

这个引理是这个文件的第一个关键结果。如果 `X` 存在一个下确界函数，则它自动存在一个上确界函数。
当然，我们也可以从一个上确界函数构造一个下确界函数，这是对偶的结果。

```lean
lemma isInf_of_isSup {S : Set X → X} (h : isSupFun S) : isInfFun (fun s ↦ S (lowerBounds s)) :=
  isSup_of_isInf (X := OrderDual X) h
```

现在，我们准备好了这个文件中的第一个主要定义：complete lattice（完备格）。

一个 complete lattice 是一个带有偏序、下确界函数和上确界函数的类型。例如，当 `X = Set Y`，带有包含关系、交集函数和并集函数时，就构成了一个 complete lattice。

```lean
class CompleteLattice (X : Type) [PartialOrder X] where
  I : Set X → X
  I_isInf : isInfFun I
  S : Set X → X
  S_isSup : isSupFun S
```
将一个 complete lattice `X` 转化为其对偶。当使用上述的 `OrderDual` 技巧时，Lean 将自动识别这种转换。

```lean
instance (X : Type) [PartialOrder X] [CompleteLattice X] : CompleteLattice (OrderDual X) where
  I := CompleteLattice.S (X := X)
  I_isInf := CompleteLattice.S_isSup (X := X)
  S := CompleteLattice.I (X := X)
  S_isSup := CompleteLattice.I_isInf (X := X)
```

现在，我们可以使用上面的第一个主要结果从偏序类型的下确界函数或上确界函数构建一个 complete lattice。

从偏序类型的下确界函数构建一个 complete lattice 结构。

```lean
def CompleteLattice.mk_of_Inf {I : Set X → X} (h : isInfFun I) : CompleteLattice X where
 I := I
 I_isInf := h
 S := fun s ↦ I (upperBounds s)
 S_isSup := isSup_of_isInf h
```

从部分有序类型的上确界函数构建一个 complete lattice 结构。

```lean
def CompleteLattice.mk_of_Sup {S : Set X → X} (h : isSupFun S) : CompleteLattice X where
 I := fun s ↦ S (lowerBounds s)
 I_isInf := isInf_of_isSup h
 S := S
 S_isSup := h
```

在本节的末尾，`X` 将是一个 complete lattice。

```lean
variable [CompleteLattice X]
```

complete lattice 上的下确界函数。

```lean
notation "Inf" => CompleteLattice.I
```

complete lattice 上的上确界函数。

```lean
notation "Sup" => CompleteLattice.S
```

现在，我们用 complete lattice 的术语重新陈述了上面证明的一些引理。

```lean
lemma lowerBound_Inf (s : Set X) : Inf s ∈ lowerBounds s :=
  (CompleteLattice.I_isInf _).lowerBound

lemma upperBound_Sup (s : Set X) : Sup s ∈ upperBounds s :=
  (CompleteLattice.S_isSup _).upperBound
```

现在我们证明一系列引理，断言 `Inf`（通过对偶性也是 `Sup`）的行为符合你的直觉。如果你认为你能够证明它们并且想要看更有趣的内容，你可以随意跳过这些引理，直接跳到 adjunction 部分。

在下面的第一个引理中，你可能会想要使用 `lowerBounds_mono_set ⦃s t : Set α⦄ (hst : s ⊆ t) : lowerBounds t ⊆ lowerBounds s`，或者在你的证明中重新证明它。

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

让我们证明 `Set` 构成一个完备格。

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

注：这一部分之后的内容是关于 adjunction 的，但可能会超出 ChatGPT 的能力进行继续翻译。
我们现在准备好了这个文件的第二个核心定义：有序类型之间的 adjunction（对应关系）。

对于有序类型之间的两个函数 `l` 和 `r`，如果 `∀ x y, l x ≤ y ↔ x ≤ r y`，则它们被称为 adjoint（对偶的）。
也可以说它们形成一个 Galois connection（Galois 联系）。
这里 `l` 代表“左”（left），`r` 代表“右”（right）。

```lean
def adjunction [PartialOrder X] [PartialOrder Y] (l : X → Y) (r : Y → X) :=
  ∀ x y, l x ≤ y ↔ x ≤ r y
```

你需要记住的一个例子是直接像与逆像之间的 adjunction。
给定 `f : α → β`，我们有：
* `Set.image f : Set α → Set β`，使用记法 `f ''`
* `Set.preimage f : Set β → Set α`，使用记法 `f ⁻¹'`
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

在该部分的剩余部分，`X` 和 `Y` 是完备格。

```lean
variable [PartialOrder X] [CompleteLattice X] [PartialOrder Y] [CompleteLattice Y]
```

现在我们来到了该文件的第二个主要定理：adjoint functor theorem（对偶函子定理）。
完备格定理（adjoint functor theorem）指出，对于完备格之间的一个函数，它是一个左 adjoint（或者右 adjoint）如果且仅如果它与 `Sup`（或者 `Inf`）可交换。

我们首先定义一个候选的右 adjoint（不对原始映射做任何假设）。

为完备格之间的映射构造一个候选的右 adjoint。
如果这个映射与 `Sup` 可交换，则它是一个真正的 adjoint，参见 `adjunction_of_Sup`。

```lean
def mk_right (l : X → Y) : Y → X := fun y ↦ Sup {x | l x ≤ y}
```

下面的定理的证明不是很长，但也不完全明显。首先，你需要理解陈述中的符号表示。`l '' s` 是 `s` 在 `l` 下的直接像，
`''` 是 `Set.image` 的表示。将光标放在 `''` 上可以看到其具体定义：

```lean
notation:50 s  " '' " f:50 => Set.image f s
```

这表示 `l` 将集合 `s` 映射到 `l` 下的元素。你还可以将光标放在 `Set.image` 上，
以查看它的定义和使用方式。解决了这些符号的含义后，你可以继续准备证明这个定理。
符号表示和使用上下文菜单中的“跳转到定义”功能将带您到定义 `Set.image` 的文件，并包含了许多与之相关的引理。在参考解答中使用的引理包括：

* `Set.image_pair : (f : α → β) (a b : α) : f '' {a, b} = {f a, f b}`
* `Set.image_preimage_subset (f : α → β) (s : Set β) : f '' (f ⁻¹' s) ⊆ s`

证明提示：一个方向很容易证明，并且不使用关键假设。对于另一个方向，你可能首先需要证明 `Monotone l`，即 `∀ ⦃a b⦄, a ≤ b → l a ≤ l b`。

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

当然，我们也可以进行相同的构造来构建左 adjoint。

为完备格之间的映射构造一个候选的左 adjoint。
如果这个映射与 `Inf` 可交换，则它是一个真正的 adjoint，参见 `adjunction_of_Inf`。

```lean
def mk_left (r : Y → X) : X → Y := fun x ↦ Inf {y | x ≤ r y}

theorem adjunction_of_Inf {r : Y → X} (h : ∀ s : Set Y, r (Inf s) = Inf (r '' s)) :
    adjunction (mk_left r) r :=
  fun x y ↦ (adjunction_of_Sup (X := OrderDual Y) (Y := OrderDual X) h y x).symm

end Adjunction

section Topology
```

在本节中，我们将上面发展的理论应用到点集拓扑（point-set topology）中。
我们的第一个目标是将给定类型 `X` 上的拓扑类型 `Topology X` 赋予完备格的结构。
带有完备格结构的拓扑类型 `Topology X`。然后，我们将任意映射 `f : X → Y` 转化为 `Topology X` 和 `Topology Y` 之间的 adjunction（对偶的）`(f⁎, f ^*)`，并使用它来构建乘积拓扑（product topology）。当然，mathlib 知道所有这些，但我们将继续构建我们自己的理论。

```lean
@[ext]
structure Topology (X : Type) where
  isOpen : Set X → Prop
  isOpen_iUnion : ∀ {ι : Type}, ∀ {s : ι → Set X}, (∀ i, isOpen (s i)) → isOpen (⋃ i, s i)
  isOpen_iInter : ∀ {ι : Type}, ∀ {s : ι → Set X}, (∀ i, isOpen (s i)) → Finite ι → isOpen (⋂ i, s i)
```

让我们对我们的定义进行两个快速的合理性检查，因为很多教材包含了冗余的定义。
这是拓扑空间定义的条件限制。

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

对于 `Topology` 定义上的 `ext` 属性，告诉 Lean 自动构建以下等价性引理：
`Topology.ext_iff (T T' : Topology X), T = T' ↔ x.isOpen = y.isOpen`。
它还将该引理注册为 `ext` 策略使用的 lemma（我们将在下面回到这个问题）。

我们使用对偶于由 `Set (Set X)` 引起的顺序的顺序对 `Topology X` 进行排序。对于这个选择有很好的理由，但超出了本教程的范围。

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

因为上述的上确界函数来自于 `OrderDual (Set (Set X))` 的上确界函数，所以它确实是一个上确界函数。我们可以陈述一个抽象引理来证明这一点，但是直接进行证明同样容易而且非常有趣。

```lean
lemma isSup_SupTop : isSupFun (SupTop : Set (Topology X) → Topology X) :=
fun _ _ ↦ ⟨fun hT _ hV _ hs ↦ hT hs hV, fun hT T' hT' _ hV ↦ hT hV T' hT'⟩
```

我们可以利用我们的抽象理论免费获取一个下确界函数，从而得到 `Topology X` 上的完备格结构。
请注意，我们的抽象理论确实在做非平凡的工作：下确界函数并*不*来自于 `OrderDual (Set (Set X))`。

```lean
instance : CompleteLattice (Topology X) := CompleteLattice.mk_of_Sup isSup_SupTop
```

让我们用完备格符号重新陈述我们对 `Sup` 的构造。证明只是简单地说“根据定义，这是正确的”。

```lean
lemma isOpen_Sup {s : Set (Topology X)} {V : Set X} : (Sup s).isOpen V ↔ ∀ T ∈ s, T.isOpen V :=
  Iff.rfl
```

现在，我们开始构建由任意映射 `f : X → Y` 引起的 `Topology X` 和 `Topology Y` 之间的 adjunction（对偶的）。我们将手动构建左 adjoint，然后调用我们的 adjoint functor 定理。

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

对于拓扑空间 `T` 和 `T'`，如果对于任意开集的原像都是开集，那么映射 `f : X → Y` 在 `T` 和 `T'` 的拓扑下就是连续的。

```lean
def Continuous (T : Topology X) (T' : Topology Y) (f : X → Y) :=  f ⁎ T ≤ T'
```

让我们检查定义确实表达了我们所声称的意思。

```lean
example (T : Topology X) (T' : Topology Y) (f : X → Y) :
  Continuous T T' f ↔ ∀ V, T'.isOpen V → T.isOpen (f ⁻¹' V) :=
Iff.rfl
```

请注意，以下证明使用了 `ext` 策略，它知道两个拓扑空间相等当且仅当它们具有相同的开集，这要归功于 `Topology` 定义中的 `ext` 属性。

```lean
lemma push_push (f : X → Y) (g : Y →Z) (T : Topology X) :
    g ⁎ (f ⁎ T) = (g ∘ f) ⁎ T := by {
  ext V
  exact Iff.rfl
}
```
我们希望找到 `f ⁎` 的一个右 adjoint，因此我们需要检查它是否与 `Sup` 可交换。
你可能希望使用 `Set.ball_image_iff : (∀ y ∈ f '' s, p y) ↔ ∀ x ∈ s, p (f x)`，
其中 "ball" 表示 "bounded for all"，即 `∀ x ∈ ...`。

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
  -- sorry
}
```
```lean
unfold Continuous ProductTopology
  rw [← CompleteLattice.I_isInf, lowerBounds_range]
  apply forall_congr'
  intro i
  unfold pull
  rw [← adjunction_of_Sup (fun s ↦ push_Sup _), push_push]
  rfl
```

```lean
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

```lean
def SubgroupInf (s : Set (Subgroup G)) : Subgroup G where
  carrier := ⋂ H ∈ s, H.carrier
  one_mem := by {
    intros H H_in_s,
    exact H.one_mem
  }
  mul_mem := by {
    intros x y hx hy H H_in_s,
    exact H.mul_mem (hx H H_in_s) (hy H H_in_s)
  }
  inv_mem := by {
    intros x hx H H_in_s,
    exact H.inv_mem (hx H H_in_s)
  }

lemma SubgroupInf_carrier (s : Set (Subgroup G)) :
  (SubgroupInf s).carrier = ⋂₀ (Subgroup.carrier '' s) :=
  by simp [SubgroupInf]

lemma isInf.lift [PartialOrder X] {f : Y → X} (hf : Function.Injective f)
  {s : Set Y} {y : Y} (hy : isInf (f '' s) (f y)) :
  @isInf Y (PartialOrder.lift f hf) s y :=
  begin
    intro y',
    erw [← hy (f y')],
    split,
    { intros h y'' H,
      rw [← H], exact h },
    { intros h x hx, exact h (show f x ∈ f '' s, from ⟨x, hx, rfl⟩) }
  end

lemma SubgroupInf_is_Inf : isInfFun (SubgroupInf : Set (Subgroup G) → Subgroup G) :=
  begin
    intros s H,
    apply isInf.lift (fun H H' ↦ (Subgroup.ext_iff H H').2),
    rw [SubgroupInf_carrier],
    apply isInfInter
  end

instance : CompleteLattice (Subgroup G) :=
  CompleteLattice.mk_of_Inf SubgroupInf_is_Inf

lemma Inf_carrier (s : Set (Subgroup G)) :
  (Inf s).carrier = ⋂₀ (Subgroup.carrier '' s) :=
  SubgroupInf_carrier s

def forget (H : Subgroup G) : Set G := H.carrier

def generate : Set G → Subgroup G := mk_left forget

lemma generate_forget_adjunction : adjunction (generate : Set G → Subgroup G) forget :=
  adjunction_of_Inf SubgroupInf_carrier

variable {G' : Type} [Group G']

def pull (f : G →* G') (H' : Subgroup G') : Subgroup G where
  carrier := f ⁻¹' H'.carrier
  one_mem := by {
    show f 1 ∈ H',
    rw [f.map_one],
    exact H'.one_mem,
  }
  mul_mem := by {
    intros x y hx hy,
    show f (x * y) ∈ H',
    rw [f.map_mul],
    exact H'.mul_mem hx hy,
  }
  inv_mem := by {
    intros x hx,
    show f x⁻¹ ∈ H',
    rw [f.map_inv],
    exact H'.inv_mem hx,
  }

lemma pull_carrier (f : G →* G') (H' : Subgroup G') :
  (pull f H').carrier = f ⁻¹' H'.carrier :=
  rfl
```
让我们非常懒地通过 adjunction 定义子群的推前映射。

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

我们的下一个具体目标是 `push_generate (f : G →* G') (S : Set G) : push f (generate S) = generate (f '' S)`，它将需要更多的抽象引理。

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

由一些集合 `S` 生成的子群在群同态的映射下的像是由 `S` 的像生成的。

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
